#!/usr/bin/env python3
"""Reproduce the PropertyF/Mathlib source and environment survey; see README.md."""
import argparse
import collections
import csv
import difflib
import hashlib
import math
import os
from pathlib import Path
import re
import statistics
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
STYLE = ROOT / 'scripts/style'
MATH = ROOT / '.lake/packages/mathlib/Mathlib'
os.chdir(ROOT)
DECL = re.compile(r'(?m)^(?P<indent>[ \t]*)(?:(?:private|protected|public|noncomputable|unsafe|partial|local|scoped)\s+)*(?P<kind>theorem|lemma|def|abbrev|opaque|instance|structure|class|inductive|axiom)\s+(?P<name>[^\s(:\[{]+)')
COMMAND = re.compile(r'(?m)^(?:@\[|(?:private |protected |public |noncomputable |unsafe |partial |local |scoped )*(?:theorem|lemma|def|abbrev|opaque|instance|structure|class|inductive|axiom)\b|(?:end|namespace|section|variable|variables|open|attribute|set_option|universe|universes|include|omit|example|run_cmd|#\w+|export|notation|infix|instance)\b)')
IMPORT = re.compile(r'^\s*(?:public\s+|meta\s+|private\s+)*import\s+(?:all\s+)?([^\s]+)', re.M)
TACTIC = re.compile(r'(?m)^\s*(?:[·|]\s*)?(?:\([^\n]*?\s+)?(intro|intros|apply|exact|refine|rfl|simp|simpa|rw|rwa|erw|convert|decide|aesop|omega|have|obtain|show|let|letI|cases|induction|constructor|ext|funext|change|calc|trans|suffices|by_cases|by_contra|rcases|rintro|subst|dsimp|unfold|push_neg|norm_num|linarith|nlinarith|ring|field_simp|assumption|trivial|first|all_goals|case|skip|congr|specialize|use|choose|classical|infer_instance|tauto|positivity)\b')
TOKENS = ['have','obtain','show','simp','erw','convert','decide','aesop','omega']

def mask(text):
    """Mask nested Lean comments and strings while preserving offsets and newlines."""
    out = list(text); n = len(text); i = 0; depth = 0; string = False
    while i < n:
        if depth:
            if text.startswith('/-', i): out[i:i+2]=[' ',' ']; depth+=1; i+=2; continue
            if text.startswith('-/', i): out[i:i+2]=[' ',' ']; depth-=1; i+=2; continue
            if text[i]!='\n': out[i]=' '
            i+=1; continue
        if string:
            if text[i]=='\\' and i+1<n:
                out[i]=' '; i+=1
                if text[i]!='\n': out[i]=' '
                i+=1; continue
            if text[i]=='"': string=False
            if text[i]!='\n': out[i]=' '
            i+=1; continue
        if text.startswith('--', i):
            while i<n and text[i]!='\n': out[i]=' '; i+=1
            continue
        if text.startswith('/-', i): out[i:i+2]=[' ',' ']; depth=1; i+=2; continue
        if text[i]=='"': out[i]=' '; string=True
        i+=1
    return ''.join(out)

def comment_lines(text):
    # Both shares count any line touched by the respective comment, including mixed code.
    comments=set(); docs=set(); depth=0; doc=False
    for ln,line in enumerate(text.splitlines(),1):
        i=0; string=False
        while i<len(line):
            if depth:
                comments.add(ln)
                if doc: docs.add(ln)
                if line.startswith('/-',i): depth+=1; i+=2; continue
                if line.startswith('-/',i): depth-=1; i+=2; doc = doc if depth else False; continue
                i+=1; continue
            if string:
                if line[i]=='\\': i+=2; continue
                if line[i]=='"': string=False
                i+=1; continue
            if line[i]=='"': string=True; i+=1; continue
            if line.startswith('--',i): comments.add(ln); break
            if line.startswith('/-',i):
                comments.add(ln); doc=line.startswith('/--',i) or line.startswith('/-!',i)
                if doc: docs.add(ln)
                depth=1; i+=2; continue
            i+=1
    return len(comments),len(docs)

def proof_delimiter(chunk):
    # Ignore assignments inside binder parentheses and `let` expressions in types.
    depth=0
    for i,c in enumerate(chunk):
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth=max(0,depth-1)
        elif c==':' and chunk[i:i+2]==':=' and depth==0:
            line=chunk[chunk.rfind('\n',0,i)+1:i]
            if re.search(r'\bletI?\b[^\n]*$',line): continue
            return i
    return -1

def parse(path, module):
    text=path.read_text(encoding='utf8'); clean=mask(text); lines=text.count('\n') + bool(text and not text.endswith('\n'))
    comments,docs=comment_lines(text); starts=list(DECL.finditer(clean)); boundaries=[m.start() for m in COMMAND.finditer(clean)]
    ds=[]
    for m in starts:
        start=m.start(); end=next((b for b in boundaries if b>start),len(text)); chunk=clean[start:end].rstrip()
        eq=proof_delimiter(chunk); kind=m['kind']; equation=False
        if kind in ('theorem','lemma'):
            em=re.search(r'(?m)^[ \t]+\|[^\n]*=>',chunk)
            if em and (eq<0 or em.start()<eq): eq=em.start(); equation=True
        stmt=chunk if eq<0 else chunk[:eq]; proof='' if eq<0 else chunk[eq+(0 if equation else 2):].strip()
        if kind in ('theorem','lemma') and eq>=0:
            tactic=bool(re.match(r'^by\b',proof)) and not equation; matches=list(TACTIC.finditer(proof)); toks={k:len(re.findall(r'\b'+k+r'\b',proof)) for k in TOKENS}
            toks['simp_only']=len(re.findall(r'\bsimp\s+only\b',proof)); toks['nonterminal_simp']=sum(1 for z in re.finditer(r'\bsimp(?:\s+only)?\b[^\n]*',proof) if proof[z.end():].strip())
        else: tactic=False; matches=[]; toks={k:0 for k in TOKENS}; toks.update(simp_only=0,nonterminal_simp=0)
        ds.append(dict(module=module,file=str(path.relative_to(ROOT)),line=text.count('\n',0,m.start())+1,kind=kind,name=m['name'],statement_lines=stmt.count('\n')+1,statement_chars=len(stmt.strip()),statement=stmt.strip(),proof_lines=(proof.count('\n')+1 if proof else 0),equation=equation,tactic=tactic,steps=len(matches)+proof.count(';'),**toks))
    # Anonymous instances are commands too, but have no stable source name.
    for im in re.finditer(r'(?m)^[ \t]*(?:(?:public|private|local|scoped|noncomputable)\s+)*instance\s*(?=[:\[])',clean):
        ds.append(dict(module=module,file=str(path.relative_to(ROOT)),line=text.count('\n',0,im.start())+1,kind='instance',name='(anonymous)',statement_lines=0,statement_chars=0,statement='',proof_lines=0,equation=False,tactic=False,steps=0,**{k:0 for k in TOKENS},simp_only=0,nonterminal_simp=0))
    imports=IMPORT.findall(clean)
    return dict(module=module,file=str(path.relative_to(ROOT)),lines=lines,comment_lines=comments,doc_lines=docs,imports=imports,declarations=ds,heartbeats=len(re.findall(r'\bset_option\s+maxHeartbeats\b',clean)))

def mod(path, root, prefix): return prefix+'.'+'.'.join(path.relative_to(root).with_suffix('').parts)
def sampled(module): return int(hashlib.sha256(module.encode()).hexdigest(),16)%10==0

def quant(values):
    v=sorted(values)
    if not v: return ['—']*6
    def q(p):
        x=(len(v)-1)*p; a=int(x); return v[a]+(v[math.ceil(x)]-v[a])*(x-a)
    return [q(.25),q(.5),q(.75),q(.9),q(.99),v[-1]]

def fmt(v): return str(round(v,2)) if isinstance(v,(float,int)) else v

def env_rows():
    with (STYLE/'.environment.tsv').open() as f: return list(csv.DictReader(f,delimiter='\t'))

def metric_table(label, a,b):
    return '| '+label+' | '+str(len(a))+' | '+' | '.join(map(fmt,quant(a)))+' | '+str(len(b))+' | '+' | '.join(map(fmt,quant(b)))+' |'

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--skip-lean',action='store_true'); args=ap.parse_args()
    projectpaths=sorted((ROOT/'PropertyF').rglob('*.lean')); mathpaths=sorted(MATH.rglob('*.lean'))
    modules=[mod(p,MATH,'Mathlib') for p in mathpaths if sampled(mod(p,MATH,'Mathlib'))]
    (STYLE/'.sample-modules').write_text('\n'.join(modules)+'\n')
    if not args.skip_lean:
        audit=(ROOT/'PropertyF/Ground/Integrate/TargetAudit.lean').read_text()
        imports='\n'.join(re.findall(r'^import all .+$',audit,re.M))+'\nimport all PropertyF\nimport all PropertyF.Ground.Integrate.ProjectAudit\nimport all PropertyF.Ground.Integrate.TargetAudit'
        generated=STYLE/'.EnvironmentRun.lean'; generated.write_text('module\npublic import Mathlib\npublic meta import Lean\n'+imports+'\n'+(STYLE/'Environment.lean').read_text())
        subprocess.run(['taskset','-c',os.environ.get('STYLE_CORES', '28-31'),'lake','env','lean',str(generated.relative_to(ROOT))],check=True,env={**os.environ,'LEAN_NUM_THREADS':'4'})
    project=[parse(p,mod(p,ROOT/'PropertyF','PropertyF')) for p in projectpaths] + [parse(ROOT/'PropertyF.lean','PropertyF')]
    project.sort(key=lambda f:f['file'])
    mathsample=[parse(p,mod(p,MATH,'Mathlib')) for p in mathpaths if sampled(mod(p,MATH,'Mathlib'))]
    mathlength=[sum(1 for _ in p.open(encoding='utf8')) for p in mathpaths]
    env=env_rows(); bymodule=collections.defaultdict(list)
    for row in env: bymodule[row['module']].append(row)
    # Match source declarations only when a module-local terminal name is unique.
    def attach(files):
        for f in files:
            endings=collections.defaultdict(list)
            for r in bymodule[f['module']]: endings[r['name'].split('.')[-1]].append(r)
            for d in f['declarations']:
                candidates=endings[d['name'].split('.')[-1]]
                if len(candidates)==1: d['env']=candidates[0]
    attach(project); attach(mathsample)
    pdecl=[d for f in project for d in f['declarations']]; mdecl=[d for f in mathsample for d in f['declarations']]
    pth=[d for d in pdecl if d['kind'] in ('lemma','theorem') and d['proof_lines']]; mth=[d for d in mdecl if d['kind'] in ('lemma','theorem') and d['proof_lines']]
    # Full-Mathlib lexical name search complements the strict type comparison.
    wanted=collections.defaultdict(list)
    for d in pth: wanted[d['name'].split('.')[-1]].append(d)
    name_matches=[]
    for path in mathpaths:
        raw=path.read_text(encoding='utf8')
        for match in DECL.finditer(raw):
            name=match['name'].split('.')[-1]
            if match['kind'] in ('lemma','theorem') and name in wanted:
                for d in wanted[name]:
                    name_matches.append((d['file'],d['line'],d['name'],str(path.relative_to(ROOT)),raw.count('\n',0,match.start())+1,match['name']))
    with (ROOT/'STYLE_NAME_MATCHES.tsv').open('w',newline='') as fp:
        w=csv.writer(fp,delimiter='\t'); w.writerow(['project_file','project_line','project_name','mathlib_file','mathlib_line','mathlib_name']); w.writerows(name_matches)
    # Graph depth is the longest chain of project-local imports, leaves at depth one.
    lookup={f['module']:f for f in project}; memo={}
    def depth(m,stack=()):
        if m in memo:return memo[m]
        if m in stack: raise RuntimeError('cycle in project import graph: '+m)
        memo[m]=1+max((depth(x,stack+(m,)) for x in lookup[m]['imports'] if x in lookup),default=0); return memo[m]
    for f in project: f['depth']=depth(f['module'])
    header=['file','lines','declarations','theorems','definitions','instances','imports','project_imports','comment_pct','doc_pct','median_proof_lines','median_statement_chars','median_tactic_steps','proof_lines_vs_mathlib_median','import_modules','depth','mathlib_p90_line_ratio','mathlib_line_percentile','cone_declarations','environment_declarations','target_cone','heartbeats']
    with (ROOT/'STYLE_FILES.tsv').open('w',newline='') as fp:
        w=csv.writer(fp,delimiter='\t'); w.writerow(header)
        for f in project:
            ds=f['declarations']; rows=bymodule[f['module']]; cone=sum(int(r['cone']) for r in rows); n=f['lines']; p90=quant(mathlength)[3]
            w.writerow([f['file'],n,len(ds),sum(d['kind'] in ('theorem','lemma') for d in ds),sum(d['kind'] in ('def','abbrev','opaque') for d in ds),sum(d['kind']=='instance' for d in ds),len(f['imports']),sum(x in lookup for x in f['imports']),round(100*f['comment_lines']/max(n,1),1),round(100*f['doc_lines']/max(n,1),1),round(statistics.median([d['proof_lines'] for d in ds if d['kind'] in ('theorem','lemma') and d['proof_lines']]),1) if any(d['kind'] in ('theorem','lemma') and d['proof_lines'] for d in ds) else '',round(statistics.median([d['statement_chars'] for d in ds if d['kind'] in ('theorem','lemma')]),1) if any(d['kind'] in ('theorem','lemma') for d in ds) else '',round(statistics.median([d['steps'] for d in ds if d['kind'] in ('theorem','lemma') and d['tactic']]),1) if any(d['kind'] in ('theorem','lemma') and d['tactic'] for d in ds) else '',round(statistics.median([d['proof_lines'] for d in ds if d['kind'] in ('theorem','lemma') and d['proof_lines']])/statistics.median([d['proof_lines'] for d in mth]),2) if any(d['kind'] in ('theorem','lemma') and d['proof_lines'] for d in ds) else '',','.join(f['imports']),f['depth'],round(n/p90,2),round(100*sum(x<=n for x in mathlength)/len(mathlength),1),cone,len(rows),'yes' if cone else 'no',f['heartbeats']])
    with (ROOT/'STYLE_DECLARATIONS.tsv').open('w',newline='') as fp:
        w=csv.DictWriter(fp,fieldnames=list(env[0]),delimiter='\t'); w.writeheader(); w.writerows(r for r in env if (r['module']=='PropertyF' or r['module'].startswith('PropertyF.')))
    lines=[]; add=lines.append
    add('# Mathlib style survey\n')
    add('Generated by `scripts/style/run.sh`. Baseline: source tree at the surveyed commit; Lean 4.35.0 and Mathlib v4.35.0. This is an observational baseline, not proof that a candidate deletion or duplicate is safe.\n')
    add(f'Project: {len(project)} files (including root `PropertyF.lean`), {sum(f["lines"] for f in project):,} lines, {len(pdecl):,} source declarations. Root `PropertyF.lean` is an aggregator. Mathlib file lengths use all {len(mathpaths):,} files. Declaration/layout comparisons use {len(mathsample):,} Mathlib files (SHA-256 of module name modulo 10 equals zero; stable, approximately 10%, unstratified), {len(mth):,} source theorems.\n')
    add('Source extraction masks nested comments and strings, identifies declaration and command lines, and estimates tactic steps from tactic-leading lines plus semicolons. It can miss syntax, local multiline commands and compound tactics; equation clauses are identified separately; proof lines include intermediate term expressions. Statement characters are masked source text, not pretty-printed elaborated types. Non-terminal `simp` is a lexical upper-bound candidate: it has any later proof text, even on a separate branch. `simp` includes `simp only`. Both comment shares count lines touched, so code/comment lines overlap; docstrings include module documentation. Source declaration matching to elaborated names is by a unique terminal name within its module, so unmatched/ambiguous declarations are excluded from elaborated comparisons.\n')
    add('## File lengths\n')
    add('| Population | n | p25 | median | p75 | p90 | p99 | max |\n|---|---:|---:|---:|---:|---:|---:|---:|')
    for label,vals in [('PropertyF',[f['lines'] for f in project]),('Mathlib',mathlength)]: add('| '+label+' | '+str(len(vals))+' | '+' | '.join(map(fmt,quant(vals)))+' |')
    add('\n| File metric | Project n | P25 | Median | P75 | P90 | P99 | Max | Mathlib sample n | P25 | Median | P75 | P90 | P99 | Max |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for label,fun in [('Declarations',lambda f:len(f['declarations'])),('Direct imports',lambda f:len(f['imports'])),('Comment line share (%)',lambda f:100*f['comment_lines']/max(f['lines'],1)),('Docstring line share (%)',lambda f:100*f['doc_lines']/max(f['lines'],1)),('maxHeartbeats commands',lambda f:f['heartbeats'])]:
        add(metric_table(label,[fun(f) for f in project],[fun(f) for f in mathsample]))
    add(f'\n{sum(f["lines"]<quant(mathlength)[0] for f in project)} project files are shorter than the Mathlib first quartile ({fmt(quant(mathlength)[0])} lines); {sum(f["lines"]>quant(mathlength)[3] for f in project)} exceed its p90 ({fmt(quant(mathlength)[3])} lines). The root aggregator and audit files are structurally exceptional. Mathlib sample has {sum(f["heartbeats"] for f in mathsample)} lexical maxHeartbeats commands across {len(mathsample)} files.')
    add('\nLargest project files (file, lines, ratio to Mathlib p90):\n')
    for f in sorted(project,key=lambda x:-x['lines'])[:15]: add(f'- `{f["file"]}`: {f["lines"]:,}, {f["lines"]/quant(mathlength)[3]:.2f}×')
    add('\nShortest project files (often candidates for consolidation, subject to coherent module boundaries):\n')
    for f in sorted(project,key=lambda x:x['lines'])[:10]: add(f'- `{f["file"]}`: {f["lines"]} lines')
    add('\n## Declaration distributions\n')
    add('Columns are p25, median, p75, p90, p99 and maximum; zeros are retained. Tactic-mode step counts apply only to `by` proofs. Elaborated sizes count structurally distinct expression nodes (shared or identical subexpressions are counted once); binders include section variables elaborated into the type. Hypotheses count top-level binders whose type Lean recognizes as a proposition, including proposition-valued instances; declarations where Lean cannot inspect a binder type are excluded from that row (999999 in the raw data).\n')
    add('| Metric | Project n | P25 | Median | P75 | P90 | P99 | Max | Mathlib n | P25 | Median | P75 | P90 | P99 | Max |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|')
    for label,key,sub in [('Proof lines','proof_lines',False),('Tactic steps','steps',True),('Statement lines','statement_lines',False),('Statement characters','statement_chars',False),('Name characters','name',False),('have per proof','have',False),('obtain per proof','obtain',False),('show per proof','show',False),('simp per proof','simp',False),('simp only per proof','simp_only',False),('Non-terminal simp candidates','nonterminal_simp',False),('erw per proof','erw',False),('convert per proof','convert',False),('decide per proof','decide',False),('aesop per proof','aesop',False),('omega per proof','omega',False)]:
        def vals(ds): return [len(d[key]) if key=='name' else d[key] for d in ds if not sub or d['tactic']]
        add(metric_table(label,vals(pth),vals(mth)))
    for label,key in [('Elaborated type nodes','type_nodes'),('Explicit binders','explicit'),('Implicit binders','implicit'),('Instance binders','instance'),('Strict implicit binders','strict'),('Hypotheses','hypotheses')]:
        add(metric_table(label,[int(d['env'][key]) for d in pth if 'env' in d and int(d['env'][key])!=999999],[int(d['env'][key]) for d in mth if 'env' in d and int(d['env'][key])!=999999]))
    for label,ds in [('PropertyF',pth),('Mathlib',mth)]:
        add(f'\n{label}: {sum(d["tactic"] for d in ds):,}/{len(ds):,} ({100*sum(d["tactic"] for d in ds)/max(len(ds),1):.1f}%) proofs start with `by`; {sum(d["equation"] for d in ds):,} use equation clauses and the remainder are classified as term mode. Source/elaboration match: {sum("env" in d for d in ds):,}/{len(ds):,} theorems.')
        add('Usage totals: '+', '.join(f'{k} {sum(d[k] for d in ds):,}' for k in TOKENS+['simp_only','nonterminal_simp'])+'.')
    add('\nLongest proof candidates:\n')
    for d in sorted(pth,key=lambda d:-d['proof_lines'])[:12]: add(f'- `{d["file"]}:{d["line"]}` `{d["name"]}`: {d["proof_lines"]} lines; {d["steps"]} estimated steps')
    add('\n## Names, options, and imports\n')
    bad=[d for d in pdecl if '__' in d['name']]; baddefs=[d for d in pdecl if d['kind'] in ('def','abbrev') and '_' in d['name'] and not d['name'].endswith('_')]
    add(f'Mathlib `linter.style.nameCheck` checks double underscores: {len(bad)} project and {sum("__" in d["name"] for d in mdecl)} sampled Mathlib source candidates. Definitions with underscores: {len(baddefs)} lexical candidates for `defsWithUnderscore` (its exceptions and private/generated checks are not reproduced). Examples: '+', '.join('`'+d['name']+'`' for d in baddefs[:12])+'.')
    add(f'`set_option maxHeartbeats` appears {sum(f["heartbeats"] for f in project)} times in {sum(bool(f["heartbeats"]) for f in project)} project files. Project-local graph: {sum(sum(i in lookup for i in f["imports"]) for f in project)} direct import edges; maximum depth {max(f["depth"] for f in project)}. This graph includes root `PropertyF.lean` and omits external modules; depth counts modules including the starting module. Deepest: '+', '.join(f'`{f["file"]}` ({f["depth"]})' for f in sorted(project,key=lambda x:-x['depth'])[:8])+'.\n')
    add('## Dependency cone and duplicate candidates\n')
    prows=[r for r in env if (r['module']=='PropertyF' or r['module'].startswith('PropertyF.'))]; inrows=[r for r in prows if r['cone']=='1']; infiles={r['module'] for r in inrows}
    add(f'Lean visits constants in both types and available values, starting at `PropertyF.Ground.target`, following `Expr.getUsedConstants` transitively through project declarations, including inductive constructors and recursor families, with the audit private imports; traversal stops at pinned upstream modules, which cannot import this project. {len(inrows):,} of {len(prows):,} elaborated project constants are in the cone, across {len(infiles)} of {len(project)} files; {len(prows)-len(inrows):,} constants and {len(project)-len(infiles)} files have no constant in this cone. Constants include compiler-generated declarations. Files marked no may still contain instances, attributes, syntax, audits, or public API needed for elaboration and must not be mechanically deleted. The result is exact for project constant references in the imported types and bodies, subject to the audit assumption that upstream modules cannot depend on the project. It is not a full upstream cone.\n')
    groups=collections.defaultdict(list)
    for d in pth:
        if 'env' in d: groups[d['env']['type_hash']].append(d)
    dup=[g for g in groups.values() if len(g)>1]
    add(f'{len(dup)} project theorem groups share a Lean expression hash of their elaborated type. Hash equality is only a search candidate, not type equality or a proof of duplication (hashes can collide; binder/universe details may differ). Examples:')
    for g in sorted(dup,key=len,reverse=True)[:15]: add('- '+'; '.join(f'`{d["file"]}:{d["line"]} {d["name"]}`' for d in g[:5]))
    hashes=collections.defaultdict(list)
    with (STYLE/'.mathlib-hashes.tsv').open() as fp:
        for row in csv.reader(fp,delimiter='\t'):
            if len(row)==3: hashes[row[0]].append(row[1])
    matches=[(d,hashes[d['env']['type_hash']]) for d in pth if 'env' in d and d['env']['type_hash'] in hashes]
    exact=collections.defaultdict(list)
    with (STYLE/'.mathlib-exact.tsv').open() as fp:
        for row in csv.reader(fp,delimiter='\t'):
            if len(row)==3: exact[row[0]].append(row[1])
    exactsource=[(d,exact[d['env']['name']]) for d in pth if 'env' in d and d['env']['name'] in exact]
    add(f'\nLean syntactic equality confirms {len(exactsource)} source theorem types match an imported Mathlib declaration type exactly (not definitional equality); replacement still requires checking imports, universes, assumptions and API. Examples:')
    for d,ms in exactsource[:15]: add(f'- `{d["file"]}:{d["line"]} {d["name"]}` → '+', '.join('`'+x+'`' for x in ms[:3]))
    pairs=list(csv.reader((STYLE/'.project-exact.tsv').open(),delimiter='\t'))
    source_names={d['env']['name']:d for d in pth if 'env' in d}
    source_pairs=[(source_names[a],source_names[b]) for a,b in pairs if a in source_names and b in source_names]
    add(f'Lean syntactic expression equality confirms {len(pairs)} project theorem pairs have identical elaborated types, including generated/private declarations; {len(source_pairs)} pairs match source theorems. Source examples:')
    for a,b in source_pairs[:15]: add(f'- `{a["file"]}:{a["line"]} {a["name"]}` / `{b["file"]}:{b["line"]} {b["name"]}`')
    add(f'\nThe full Mathlib source name scan produced {len(name_matches)} same-terminal-name pairs in `STYLE_NAME_MATCHES.tsv`. Names alone do not establish related statements and raw scanning can include commented text.')
    old_norm = any(d['file'] == 'PropertyF/BraidAlgebra.lean' and
                   d['name'] == 'norm_eq_one_of_pow_eq_one' for d in pth)
    if old_norm:
        add('The project theorem `PropertyF.norm_eq_one_of_pow_eq_one` follows directly from `Complex.norm_eq_one_of_pow_eq_one` with the hypotheses reversed. `scripts/style/ExistingMathlib.lean` independently checks that application, which strict expression equality misses.\n')
    else:
        add('The former project theorem `PropertyF.norm_eq_one_of_pow_eq_one` has been removed in favor of `Complex.norm_eq_one_of_pow_eq_one`. `scripts/style/ExistingMathlib.lean` independently checks the application with the hypotheses reversed.\n')
    add(f'\n{len(matches)} source theorems have a type hash shared with an imported Mathlib declaration. These are unverified candidates, not established Mathlib replacements; this is not semantic `exact?` search. Imported Mathlib theorem bodies are hidden and appear axiom-shaped; actual axiom declarations are also included, so inspect source and trust assumptions before replacement. Examples:')
    for d,ms in matches[:15]: add(f'- `{d["file"]}:{d["line"]} {d["name"]}` → '+', '.join('`'+x+'`' for x in ms[:3]))
    # Pair same-named lemmas across modules; similarity is a review heuristic.
    named=collections.defaultdict(list)
    for d in pth: named[d['name'].split('.')[-1]].append(d)
    near=[]
    for ds in named.values():
        for i,a in enumerate(ds):
            for b in ds[i+1:]:
                if a['module']==b['module']: continue
                sa=re.sub(r'\s+',' ',a['statement']); sb=re.sub(r'\s+',' ',b['statement'])
                ratio=difflib.SequenceMatcher(None,sa,sb,autojunk=False).ratio()
                if ratio>=.8: near.append((ratio,a,b))
    near.sort(key=lambda x:-x[0])
    add(f'\n{len(near)} same-named theorem pairs in different modules have at least 0.8 normalized source-statement similarity. These are near-duplicate candidates only; namespaces, implicit context, types, and meaning can differ:')
    for ratio,a,b in near[:15]: add(f'- {ratio:.2f}: `{a["file"]}:{a["line"]} {a["name"]}` / `{b["file"]}:{b["line"]} {b["name"]}`')
    reductions=[d for d in pdecl if d['name'].startswith('target_of_')]
    add(f'\nThere are {len(reductions)} source declarations named `target_of_*`; {sum(d.get("env",{}).get("cone")=="1" for d in reductions)} matched declarations are in the target cone. Treat these as a reduction chain to review, not automatic dead code. Directories named `Centre*` contain {sum(f["file"].split("/")[2].startswith("Centre") for f in project if len(f["file"].split("/"))>2)} files, including {sum("/Centre/" in f["file"] for f in project)} in `Centre/`. Legacy/compatibility file names: '+', '.join('`'+f['file']+'`' for f in project if re.search(r'Legacy|Compat',f['file'],re.I))+'.')
    add('\nReduction inventory (source name; cone status is unknown if the source name did not match one elaborated constant):')
    for d in reductions:
        status=('yes' if d['env']['cone']=='1' else 'no') if 'env' in d else 'unknown'
        add(f'- `{d["file"]}:{d["line"]}` `{d["name"]}`: {status}')
    add('\nCentre-family inventory (file counts and files containing a cone constant):')
    dirs=collections.defaultdict(list)
    for f in project:
        parts=f['file'].split('/')
        if len(parts)>3 and parts[1]=='Ground' and parts[2].startswith('Centre'): dirs[parts[2]].append(f)
    for name,fs in sorted(dirs.items()):
        add(f'- `{name}/`: {len(fs)} files, {sum(f["module"] in infiles for f in fs)} with a cone constant')
    add('The similar directory names alone do not prove duplicate definitions. Compare the exact-type and same-name candidates above, then inspect instances, namespaces and imported centre constructions before consolidating. Legacy-named bridges may intentionally connect the older numerical interface to the ground-level structures; no bridge is classified as redundant solely from its filename.\n')
    buildlint=ROOT/'STYLE_LINT_BUILD.txt'
    if buildlint.exists():
        bdata=buildlint.read_text(); bwarns=re.findall(r'^warning: .*',bdata,re.M); bkinds=collections.Counter(re.findall(r'linter\.[A-Za-z0-9_.]+',bdata))
        add(f'\n## Full build lint output\n\nThe full `lake build PropertyF` emitted {len(bwarns)} warning blocks under the Mathlib default enabled linters; complete warning blocks are recorded in `STYLE_LINT_BUILD.txt`. Linter note counts: '+', '.join(f'`{k}` {v}' for k,v in bkinds.most_common(12))+'. This is not a full `linter.all` or `#lint` run.\n')
    envlint=ROOT/'STYLE_LINT_ENV.txt'
    if envlint.exists():
        edata=envlint.read_text(); headline=next(iter(edata.splitlines()),'')
        categories=re.findall(r'The `([^`]+)` linter reports:',edata)
        add(f'\n## Project environment lint\n\n`#lint in PropertyF` (all default environment linters, including slow linters) reported: `{headline}`. Findings fall under '+', '.join('`'+k+'`' for k in categories)+'. Full output is in `STYLE_LINT_ENV.txt`; Lean returns a nonzero exit when lint findings exist. Declaration timing was not collected.\n')
    else: add('\n## Environment lint\n\nEnvironment lint output is unavailable.\n')
    add('\nThe scorecard includes all project source files including the root aggregator; its `target_cone` field means at least one elaborated constant from that module is reachable, not that every declaration in the module is needed. The Mathlib percentile compares line counts with all Mathlib files.\n')
    (ROOT/'STYLE_REPORT.md').write_text('\n'.join(lines))
    print('Wrote STYLE_REPORT.md and STYLE_FILES.tsv')

if __name__=='__main__': main()
