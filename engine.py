# tiny-chess-01 source: alpha-beta + quiescence, fixed nodes, no clock, no randomness.
import json,os,sys,urllib.request
from urllib.error import HTTPError
ENV_URL=os.environ.get("MAKEFUN_ENV_URL") or sys.exit("MAKEFUN_ENV_URL is not set")
BUDGET=100000
MATE=100000
INF=1000000
P,N,B,R,Q,K=1,2,3,4,5,6
VAL=(0,100,320,330,500,900,0)
PHASE=(0,0,1,1,2,4,0)
KN_OFF=(-33,-31,-18,-14,14,18,31,33)
KG_OFF=(-17,-16,-15,-1,1,15,16,17)
DIAG=(-17,-15,15,17)
ORTH=(-16,-1,1,16)
# Piece-square tables, a8..h1, centipawns.
PAWN=(0,0,0,0,0,0,0,0,
50,50,50,50,50,50,50,50,
10,10,20,30,30,20,10,10,
5,5,10,25,25,10,5,5,
0,0,0,20,20,0,0,0,
5,-5,-10,0,0,-10,-5,5,
5,10,10,-20,-20,10,10,5,
0,0,0,0,0,0,0,0)
KNIGHT=(-50,-40,-30,-30,-30,-30,-40,-50,
-40,-20,0,0,0,0,-20,-40,
-30,0,10,15,15,10,0,-30,
-30,5,15,20,20,15,5,-30,
-30,0,15,20,20,15,0,-30,
-30,5,10,15,15,10,5,-30,
-40,-20,0,5,5,0,-20,-40,
-50,-40,-30,-30,-30,-30,-40,-50)
BISHOP=(-20,-10,-10,-10,-10,-10,-10,-20,
-10,0,0,0,0,0,0,-10,
-10,0,5,10,10,5,0,-10,
-10,5,5,10,10,5,5,-10,
-10,0,10,10,10,10,0,-10,
-10,10,10,10,10,10,10,-10,
-10,5,0,0,0,0,5,-10,
-20,-10,-10,-10,-10,-10,-10,-20)
ROOK=(0,0,0,0,0,0,0,0,
5,10,10,10,10,10,10,5,
-5,0,0,0,0,0,0,-5,
-5,0,0,0,0,0,0,-5,
-5,0,0,0,0,0,0,-5,
-5,0,0,0,0,0,0,-5,
-5,0,0,0,0,0,0,-5,
0,0,0,5,5,0,0,0)
QUEEN=(-20,-10,-10,-5,-5,-10,-10,-20,
-10,0,0,0,0,0,0,-10,
-10,0,5,5,5,5,0,-10,
-5,0,5,5,5,5,0,-5,
0,0,5,5,5,5,0,-5,
-10,5,5,5,5,5,0,-10,
-10,0,5,0,0,0,0,-10,
-20,-10,-10,-5,-5,-10,-10,-20)
KINGMG=(-30,-40,-40,-50,-50,-40,-40,-30,
-30,-40,-40,-50,-50,-40,-40,-30,
-30,-40,-40,-50,-50,-40,-40,-30,
-30,-40,-40,-50,-50,-40,-40,-30,
-20,-30,-30,-40,-40,-30,-30,-20,
-10,-20,-20,-20,-20,-20,-20,-10,
20,20,0,0,0,0,20,20,
20,30,10,0,0,10,30,20)
KINGEG=(-50,-40,-30,-20,-20,-30,-40,-50,
-30,-20,-10,0,0,-10,-20,-30,
-30,-10,20,30,30,20,-10,-30,
-30,-10,30,40,40,30,-10,-30,
-30,-10,30,40,40,30,-10,-30,
-30,-10,20,30,30,20,-10,-30,
-30,-30,0,0,0,0,-30,-30,
-50,-30,-30,-30,-30,-30,-30,-50)
# 0x88 board: a8=0 .. h1=119, off-board iff sq & 0x88.
TAB={}
for _pc,_t in ((P,PAWN),(N,KNIGHT),(B,BISHOP),(R,ROOK),(Q,QUEEN),(K,KINGMG)):
    _a=[0]*128
    for _sq in range(128):
        if not _sq&0x88: _a[_sq]=_t[(_sq>>4)*8+(_sq&7)]
    TAB[_pc]=_a
KMG=TAB[K]
KEG=[0]*128
for _sq in range(128):
    if not _sq&0x88: KEG[_sq]=KINGEG[(_sq>>4)*8+(_sq&7)]
board=[0]*128
side=True
castling=0
ep=-1
wk=116
bk=4
undo=[]
nodes=0
tt={}
killers=[[0,0] for _ in range(128)]
history=[0]*16384
class Timeout(Exception):
    pass
def attacked(sq,w):
    if w:
        for t in (sq+15,sq+17):
            if not t&0x88 and board[t]==P: return True
        pn,pb,pr,pq,pk=N,B,R,Q,K
    else:
        for t in (sq-15,sq-17):
            if not t&0x88 and board[t]==-P: return True
        pn,pb,pr,pq,pk=-N,-B,-R,-Q,-K
    for o in KN_OFF:
        t=sq+o
        if not t&0x88 and board[t]==pn: return True
    for o in KG_OFF:
        t=sq+o
        if not t&0x88 and board[t]==pk: return True
    for o in DIAG:
        t=sq+o
        while not t&0x88:
            p=board[t]
            if p:
                if p==pb or p==pq: return True
                break
            t+=o
    for o in ORTH:
        t=sq+o
        while not t&0x88:
            p=board[t]
            if p:
                if p==pr or p==pq: return True
                break
            t+=o
    return False
def gen_moves(caps_only=False):
    moves=[]
    for sq in range(128):
        if sq&0x88: continue
        p=board[sq]
        if p==0 or (p>0)!=side: continue
        ap=abs(p)
        if ap==P:
            d=-16 if p>0 else 16
            last=0 if p>0 else 7
            t=sq+d
            if not t&0x88 and board[t]==0:
                if (t>>4)==last:
                    for pro in (Q,N,B,R):
                        moves.append(sq|(t<<7)|(pro<<14))
                elif not caps_only:
                    moves.append(sq|(t<<7))
                    if (sq>>4)==(6 if p>0 else 1):
                        t2=sq+2*d
                        if board[t2]==0: moves.append(sq|(t2<<7))
            for dd in (d-1,d+1):
                t=sq+dd
                if t&0x88: continue
                q=board[t]
                if q and (q>0)!=(p>0):
                    if (t>>4)==last:
                        for pro in (Q,N,B,R):
                            moves.append(sq|(t<<7)|(pro<<14))
                    else: moves.append(sq|(t<<7))
                elif t==ep: moves.append(sq|(t<<7))
        elif ap==N or ap==K:
            offs=KN_OFF if ap==N else KG_OFF
            for o in offs:
                t=sq+o
                if t&0x88: continue
                q=board[t]
                if q==0:
                    if not caps_only: moves.append(sq|(t<<7))
                elif (q>0)!=(p>0): moves.append(sq|(t<<7))
        else:
            offs=DIAG if ap==B else ORTH if ap==R else DIAG+ORTH
            for o in offs:
                t=sq+o
                while not t&0x88:
                    q=board[t]
                    if q==0:
                        if not caps_only: moves.append(sq|(t<<7))
                        t+=o
                        continue
                    if (q>0)!=(p>0): moves.append(sq|(t<<7))
                    break
    if not caps_only:
        if side:
            if castling&1 and board[117]==0 and board[118]==0 and board[116]==K and board[119]==R and not attacked(116,False) and not attacked(117,False) and not attacked(118,False):
                moves.append(116|(118<<7))
            if castling&2 and board[115]==0 and board[114]==0 and board[113]==0 and board[116]==K and board[112]==R and not attacked(116,False) and not attacked(115,False) and not attacked(114,False):
                moves.append(116|(114<<7))
        else:
            if castling&4 and board[5]==0 and board[6]==0 and board[4]==-K and board[7]==-R and not attacked(4,True) and not attacked(5,True) and not attacked(6,True):
                moves.append(4|(6<<7))
            if castling&8 and board[3]==0 and board[2]==0 and board[1]==0 and board[4]==-K and board[0]==-R and not attacked(4,True) and not attacked(3,True) and not attacked(2,True):
                moves.append(4|(2<<7))
    return moves
def make(m):
    global castling,ep,side,wk,bk
    frm=m&127; to=(m>>7)&127; pro=(m>>14)&7
    p=board[frm]
    cap=board[to]; csq=to
    if abs(p)==P and to==ep and cap==0:
        csq=to+16 if p>0 else to-16
        cap=board[csq]; board[csq]=0
    undo.append((m,cap,csq,castling,ep))
    board[frm]=0
    board[to]=(pro if p>0 else -pro) if pro else p
    if p==K or p==-K:
        if p>0: wk=to
        else: bk=to
        if to-frm==2: board[to-1]=board[to+1]; board[to+1]=0
        elif frm-to==2: board[to+1]=board[to-2]; board[to-2]=0
        castling&=~3 if p>0 else ~12
    if frm==112 or to==112: castling&=~2
    if frm==119 or to==119: castling&=~1
    if frm==0 or to==0: castling&=~8
    if frm==7 or to==7: castling&=~4
    ep=(frm+to)//2 if abs(p)==P and abs(to-frm)==32 else -1
    side=not side
def unmake():
    global castling,ep,side,wk,bk
    m,cap,csq,co,eo=undo.pop()
    frm=m&127; to=(m>>7)&127; pro=(m>>14)&7
    p=board[to]
    board[to]=0
    board[frm]=(P if p>0 else -P) if pro else p
    if cap: board[csq]=cap
    if p==K or p==-K:
        if p>0: wk=frm
        else: bk=frm
        if to-frm==2: board[to+1]=board[to-1]; board[to-1]=0
        elif frm-to==2: board[to-2]=board[to+1]; board[to+1]=0
    castling=co; ep=eo; side=not side
def mscore(m,ply,ttm):
    if m==ttm: return 1<<30
    frm=m&127; to=(m>>7)&127; pro=(m>>14)&7
    if pro: return (1<<20)+VAL[pro]
    cap=board[to]
    if cap: return (1<<20)+10*VAL[abs(cap)]-VAL[abs(board[frm])]//10
    if abs(board[frm])==P and to==ep: return (1<<20)+10*VAL[P]
    if m==killers[ply][0] or m==killers[ply][1]: return 1<<19
    return history[frm*128+to]
def evaluate():
    s=0; ph=0; wb=0; bb=0
    for sq in range(128):
        if sq&0x88: continue
        p=board[sq]
        if p>0:
            s+=VAL[p]+TAB[p][sq]
            ph+=PHASE[p]
            if p==B: wb+=1
        elif p<0:
            s-=VAL[-p]+TAB[-p][sq^0x70]
            ph+=PHASE[-p]
            if p==-B: bb+=1
    s+=30*(wb==2)-30*(bb==2)
    if ph>24: ph=24
    w=24-ph
    s+=(KMG[wk]*ph+KEG[wk]*w)//24
    s-=(KMG[bk^0x70]*ph+KEG[bk^0x70]*w)//24
    return s if side else -s
def qsearch(alpha,beta,ply):
    global nodes
    nodes+=1
    if nodes>=BUDGET: raise Timeout
    if ply>=64: return evaluate()
    if attacked(wk if side else bk,not side):
        moves=gen_moves()
        moves.sort(key=lambda m:-mscore(m,ply,0))
        legal=0
        for m in moves:
            make(m)
            if attacked(wk if not side else bk,side):
                unmake()
                continue
            legal+=1
            try: s=-qsearch(-beta,-alpha,ply+1)
            finally: unmake()
            if s>alpha: alpha=s
            if alpha>=beta: break
        return -MATE+ply if legal==0 else alpha
    stand=evaluate()
    if stand>=beta: return beta
    if stand>alpha: alpha=stand
    caps=gen_moves(True)
    caps.sort(key=lambda m:-mscore(m,ply,0))
    for m in caps:
        to=(m>>7)&127; pro=(m>>14)&7
        v=VAL[abs(board[to])] if board[to] else 100
        if pro: v+=VAL[pro]-VAL[P]
        if stand+v+200<alpha: continue
        make(m)
        if attacked(wk if not side else bk,side):
            unmake()
            continue
        try: s=-qsearch(-beta,-alpha,ply+1)
        finally: unmake()
        if s>alpha: alpha=s
        if alpha>=beta: break
    return alpha
def search(alpha,beta,depth,ply):
    global nodes,ep,side
    nodes+=1
    if nodes>=BUDGET: raise Timeout
    if depth<=0: return qsearch(alpha,beta,ply)
    key=None; ttm=0
    if depth>=2:
        key=(tuple(board),side,castling,ep)
        e=tt.get(key)
        if e:
            ed,es,ef,em=e
            if ed>=depth:
                if ef==0: return es
                if ef==1 and es>=beta: return es
                if ef==2 and es<=alpha: return es
            ttm=em
    in_check=attacked(wk if side else bk,not side)
    if in_check and ply<64: depth+=1
    if depth>=3 and not in_check and beta<MATE:
        _hp=0
        for _sq in range(128):
            _p=board[_sq]
            if _p and (_p>0)==side and 2<=abs(_p)<6: _hp=1; break
        if _hp:
            _e=ep; side=not side; ep=-1
            try: _s=-search(-beta,-beta+1,depth-3,ply+1)
            finally: side=not side; ep=_e
            if _s>=beta: return beta
    moves=gen_moves()
    moves.sort(key=lambda m:-mscore(m,ply,ttm))
    best=-INF; bestm=0; legal=0; orig_alpha=alpha
    for m in moves:
        to=(m>>7)&127; frm=m&127
        is_cap=board[to]!=0 or (abs(board[frm])==P and to==ep)
        is_pro=(m>>14)&7
        make(m)
        if attacked(wk if not side else bk,side):
            unmake()
            continue
        legal+=1
        try: s=-search(-beta,-alpha,depth-1,ply+1)
        finally: unmake()
        if s>best: best=s; bestm=m
        if s>alpha: alpha=s
        if alpha>=beta:
            if not is_cap and not is_pro:
                if killers[ply][0]!=m:
                    killers[ply][1]=killers[ply][0]
                    killers[ply][0]=m
                history[frm*128+to]+=depth*depth
            break
    if legal==0: return -MATE+ply if in_check else 0
    if key is not None:
        if best<=orig_alpha: flag=2
        elif best>=beta: flag=1
        else: flag=0
        tt[key]=(depth,best,flag,bestm)
    return best
def root_best():
    global nodes,tt
    tt={}; nodes=0
    moves=gen_moves()
    legal=[]
    for m in moves:
        make(m)
        if attacked(wk if not side else bk,side):
            unmake()
            continue
        unmake()
        legal.append(m)
    if not legal: return 0
    legal.sort(key=lambda m:-mscore(m,0,0))
    bestm=legal[0]
    try:
        for depth in range(1,13):
            legal.sort(key=lambda m:(m!=bestm,-mscore(m,0,0)))
            alpha=-INF; bs=-INF; bm=bestm
            for m in legal:
                make(m)
                try: s=-search(-INF,-alpha,depth-1,1)
                finally: unmake()
                if s>bs: bs=s; bm=m
                if s>alpha: alpha=s
            bestm=bm
    except Timeout:
        pass
    return bestm
def sq_uci(sq):
    return chr(97+(sq&7))+str(8-(sq>>4))
def uci(m):
    s=sq_uci(m&127)+sq_uci((m>>7)&127)
    pro=(m>>14)&7
    return s+"  nbrq"[pro] if pro else s
def sq_from_uci(s):
    return (8-int(s[1]))*16+(ord(s[0])-97)
def parse_uci_move(u):
    frm=sq_from_uci(u[:2]); to=sq_from_uci(u[2:4])
    pro="nbrq".find(u[4])+2 if len(u)==5 else 0
    return frm|(to<<7)|(pro<<14)
def parse_fen(fen):
    global board,side,castling,ep,wk,bk
    board=[0]*128
    parts=fen.split()
    mp={"p":P,"n":N,"b":B,"r":R,"q":Q,"k":K}
    for r,row in enumerate(parts[0].split("/")):
        f=0
        for c in row:
            if c.isdigit(): f+=int(c)
            else:
                p=mp[c.lower()]
                if c.islower(): p=-p
                sq=r*16+f
                board[sq]=p
                if p==K: wk=sq
                elif p==-K: bk=sq
                f+=1
    side=parts[1]=="w"
    castling=0
    if parts[2]!="-":
        if "K" in parts[2]: castling|=1
        if "Q" in parts[2]: castling|=2
        if "k" in parts[2]: castling|=4
        if "q" in parts[2]: castling|=8
    ep=-1 if parts[3]=="-" else sq_from_uci(parts[3])
    undo.clear()
def post(path,body):
    req=urllib.request.Request(ENV_URL+path,data=json.dumps(body).encode(),headers={"content-type":"application/json"})
    try:
        with urllib.request.urlopen(req) as res: return json.load(res)
    except HTTPError as e:
        sys.exit(f"{path}: HTTP {e.code} {e.read().decode(errors='replace')}")
while True:
    g=post("/game",{})
    if g["status"]=="done": break
    while g["status"]=="your_move":
        parse_fen(g["fen"])
        m=root_best()
        u=uci(m) if m else None
        if not u or u not in g["legal_moves"]:
            u=g["legal_moves"][0]
        g=post("/move",{"game":g["game"],"move":u})
