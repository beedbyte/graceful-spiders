from pathlib import Path
import sys
from bound_sha import bound_sha
H=Path(__file__).resolve().parent
targets={
 'D8-author':'graceful-q10-gap-fill-beyond-d7-2026-10-09-a/check.py',
 'D8-audit':'graceful-q10-gap-fill-independent-2026-10-09-a/audit.py',
 'D7-author':'graceful-ten-elevenths-global-2026-10-09-a/verify.py',
 'D7-audit':'graceful-ten-elevenths-independent-2026-10-09-a/audit.py',
 'D7-author-check':'graceful-ten-elevenths-independent-2026-10-09-a/check_author.py'}
if len(sys.argv)!=2 or sys.argv[1] not in targets:raise RuntimeError('Select one documented check target')
target=sys.argv[1];source=H/'research-audits'/targets[target]
code=source.read_text(encoding='utf-8')
roots={'D7-author':'ROOT','D8-author':'ROOT','D8-audit':'W'}
if target in roots:
 root=roots[target]
 old='hashlib.sha256(('+root+'/rel).read_bytes()).hexdigest()'
 if code.count(old)!=1:raise RuntimeError('Provenance overlay no longer matches frozen source')
 code=code.replace(old,'bound_sha('+root+'/rel)')
sys.path.insert(0,str(source.parent));sys.argv=[str(source)]
exec(compile(code,str(source),'exec'),{'__name__':'__main__','__file__':str(source),'bound_sha':bound_sha})
