#!/usr/bin/env python3
"""Source parser from the October 27 style survey; deliberately retains its methodology."""
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

def parse(path, module, include_inline_attributes=False, count_all_proofs=False):
    text=path.read_text(encoding='utf8'); clean=mask(text);
    if include_inline_attributes:
        # Preserve line lengths and offsets while moving same-line attributes
        # after the command; only the masked analysis text is rewritten.
        pattern = r'(?m)^([ \t]*)@\[[^\n]*?\][ \t]+(?=(?:(?:private|protected|public|noncomputable|unsafe|partial|local|scoped)\s+)*(?:theorem|lemma|def|abbrev|opaque|instance)\b)([^\n]*)'
        clean = re.sub(pattern, lambda m: m[1] + m[2] + ' ' * (len(m[0]) - len(m[1]) - len(m[2])), clean)
    lines=text.count('\n') + bool(text and not text.endswith('\n'))
    comments,docs=comment_lines(text); starts=list(DECL.finditer(clean)); boundaries=[m.start() for m in COMMAND.finditer(clean)]
    ds=[]
    for m in starts:
        start=m.start(); end=next((b for b in boundaries if b>start),len(text)); chunk=clean[start:end].rstrip()
        eq=proof_delimiter(chunk); kind=m['kind']; equation=False
        if kind in ('theorem','lemma'):
            em=re.search(r'(?m)^[ \t]+\|[^\n]*=>',chunk)
            if em and (eq<0 or em.start()<eq): eq=em.start(); equation=True
        stmt=chunk if eq<0 else chunk[:eq]; proof='' if eq<0 else chunk[eq+(0 if equation else 2):].strip()
        if (kind in ('theorem','lemma') or count_all_proofs) and eq>=0:
            tactic=bool(re.match(r'^by\b',proof)) and not equation; matches=list(TACTIC.finditer(proof)); toks={k:len(re.findall(r'\b'+k+r'\b',proof)) for k in TOKENS}
            toks['simp_only']=len(re.findall(r'\bsimp\s+only\b',proof)); toks['nonterminal_simp']=sum(1 for z in re.finditer(r'\bsimp(?:\s+only)?\b[^\n]*',proof) if proof[z.end():].strip())
        else: tactic=False; matches=[]; toks={k:0 for k in TOKENS}; toks.update(simp_only=0,nonterminal_simp=0)
        ds.append(dict(module=module,file=str(path.relative_to(ROOT)),line=text.count('\n',0,m.start())+1,kind=kind,name=m['name'],statement_lines=stmt.count('\n')+1,statement_chars=len(stmt.strip()),statement=stmt.strip(),proof_lines=(proof.count('\n')+1 if proof else 0),equation=equation,tactic=tactic,steps=len(matches)+proof.count(';'),**toks))
    if count_all_proofs:
        # Anonymous proposition-valued instances can elaborate to theorems.
        # Give them a source identity; the dashboard separately resolves Lean's
        # generated name when it is unique in the module.
        for im in re.finditer(r'(?m)^[ \t]*(?:(?:public|private|local|scoped|noncomputable)\s+)*instance\s*(?=[:\[(])', clean):
            start = im.start()
            end = next((b for b in boundaries if b > start), len(text))
            chunk = clean[start:end].rstrip()
            eq = proof_delimiter(chunk)
            if eq < 0:
                continue
            proof = chunk[eq + 2:].strip()
            if not proof:
                continue
            ds.append(dict(module=module, file=str(path.relative_to(ROOT)),
                line=text.count('\n', 0, start)+1, kind='instance', name='(anonymous)',
                statement_lines=0, statement_chars=0, statement='',
                proof_lines=proof.count('\n')+1, equation=False,
                tactic=bool(re.match(r'^by\b', proof)),
                steps=len(list(TACTIC.finditer(proof)))+proof.count(';'),
                **{k:0 for k in TOKENS}, simp_only=0, nonterminal_simp=0))
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
