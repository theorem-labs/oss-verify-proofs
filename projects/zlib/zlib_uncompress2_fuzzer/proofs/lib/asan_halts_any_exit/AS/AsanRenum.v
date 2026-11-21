(* NEW text AS/AsanRenum, proposal md5 *)
(* moves the r30q2 start-up plans to the start state.
   - rplan / racs / rshape shift every variable >= base by k (expressions, facts, states, the PBump / PLoop / PVia /
     PRename variable bounds). The r30q2 plans' literal variables are 5, 6 and >= 78, so base 15 / k 4 moves exactly the
     plan-made variables (the start block grew by V_G, V_GID, V_EHDR, V_EFN).
   - shift_atr8 / shift_atr8_shape move the AT_RANDOM shadow case splits (on e_atr8) with the layout: the shadow index of
     the AT_RANDOM bytes is e_atr8 + 24 at r30q2 and e_atr8 + 58 + 4 r at .
   The plan checker is the judge: a wrong move can only make a certificate fail. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AS Require Import AxSymExec3 AsanPlanCore AsanPlan.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Section Renum.
Variable base k : nat.
Definition rv (n : nat) : nat := if Nat.ltb n base then n else (n + k)%nat.
Fixpoint re (e : expr) : expr :=
  match e with
  | ELit z => ELit z | EVar n => EVar (rv n)
  | EAlu op a b => EAlu op (re a) (re b) | EAluw op a b => EAluw op (re a) (re b)
  | EMd op a b => EMd op (re a) (re b) | EMdw op a b => EMdw op (re a) (re b)
  | EExt sx lo n e => EExt sx lo n (re e) | EBlob sx kk i n => EBlob sx kk i n
  end.
Definition rsa (a : saddr) : saddr := SA (re (a_base a)) (a_off a).
Definition rk (K : kentry) : kentry :=
  match K with
  | KWord a w v => KWord (rsa a) w (re v) | KZero a n => KZero (rsa a) (re n) | KBlob a n kk => KBlob (rsa a) (re n) kk
  | KImg lo hi => KImg lo hi | KAlign e m => KAlign (re e) m | KRange e lo hi => KRange (re e) lo hi
  | KWr a n => KWr (rsa a) (re n) | KDisj a1 n1 a2 n2 => KDisj (rsa a1) (re n1) (rsa a2) (re n2)
  | KFill a n c => KFill (rsa a) (re n) c | KUnk a n => KUnk (rsa a) (re n)
  end.
Definition rse (s : sentry) : sentry := SE (rsa (e_addr s)) (e_width s) (re (e_val s)).
Definition rss (ss : sym_state) : sym_state :=
  SSR (s_pc ss) (map re (s_regs ss)) (map rse (s_log ss)) (map rk (s_know ss)) (rv (s_next ss)) (option_map rsa (s_resv ss)).
Definition ram (m : amap) : amap := AM (re (am_base m)) (re (am_len m)) (am_kind m).
Definition rfd (f : afd) : afd := match f with FdStd => FdStd | FdFile kk len off => FdFile kk (re len) (re off) | FdDir => FdDir end.
Definition rpair (p : expr * expr) : expr * expr := (re (fst p), re (snd p)).
Definition racs (cs : acs) : acs :=
  ACS (rss (a_ss cs)) (map ram (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs) (map rpair (a_vis cs)) (map rpair (a_ghost cs))
      (a_abytes cs) (re (a_brk cs)) (rfd (a_fd cs)) (a_tidset cs).
Fixpoint rshape (s : shape) : shape :=
  match s with
  | SNil => SNil | SExit c => SExit c | SEmitP fd ps s' => SEmitP fd ps (rshape s') | SAlt2 a b => SAlt2 (rshape a) (rshape b)
  | SCase e m a b => SCase (re e) m (rshape a) (rshape b) | SHole h => SHole h | SNext => SNext
  end.
Fixpoint rplan (p : plan) : plan :=
  match p with
  | PRun st k0 => PRun st (rplan k0)
  | PSplit e m k1 k2 => PSplit (re e) m (rplan k1) (rplan k2)
  | PCase2 e m k1 k2 => PCase2 (re e) m (rplan k1) (rplan k2)
  | PCaseDisj b1 b2 k1 k2 => PCaseDisj (re b1) (re b2) (rplan k1) (rplan k2)
  | PShDisj b1 n1 b2 n2 k0 => PShDisj (re b1) (re n1) (re b2) (re n2) (rplan k0)
  | PContra => PContra
  | PFact K k0 => PFact (rk K) (rplan k0)
  | PJoin b off n k0 => PJoin (re b) off n (rplan k0)
  | PForget ixs k0 => PForget ixs (rplan k0)
  | PDropRange b n k0 => PDropRange (re b) (re n) (rplan k0)
  | PGcKeep ws k0 => PGcKeep (map rpair ws) (rplan k0)
  | PBump m k0 => PBump (rv m) (rplan k0)
  | PHavoc rs k0 => PHavoc rs (rplan k0)
  | PHavocBig K k0 => PHavocBig K (rplan k0)
  | PFresh r logc b0 k0 => PFresh r logc (option_map re b0) (rplan k0)
  | PSys y k0 => PSys y (rplan k0)
  | PMmap a b => PMmap (rplan a) (rplan b)
  | PMmapIn a b c => PMmapIn (rplan a) (rplan b) (rplan c)
  | PMprotect a b => PMprotect (rplan a) (rplan b)
  | PBrk2 a b => PBrk2 (rplan a) (rplan b)
  | PX x args k0 => PX x (map re args) (rplan k0)
  | PExt id args k0 => PExt id (map re args) (rplan k0)
  | PEmit id args k0 => PEmit id (map re args) (rplan k0)
  | PExt2 id args k1 k2 => PExt2 id (map re args) (rplan k1) (rplan k2)
  | PLoop J N inv body k0 => PLoop (rv J) (re N) (racs inv) (rplan body) (rplan k0)
  | PNext => PNext | PHandoff h => PHandoff h | PExit => PExit | PSpin => PSpin
  | PFog i sz k0 => PFog i sz (rplan k0)
  | PFogNew i sz k0 => PFogNew i sz (rplan k0)
  | PGhost b n k0 => PGhost (re b) (re n) (rplan k0)
  | PUnvis b n k0 => PUnvis (re b) (re n) (rplan k0)
  | PHavocBrk lo hi k0 => PHavocBrk lo hi (rplan k0)
  | PIntro lo hi k0 => PIntro lo hi (rplan k0)
  | PDiamond jpc rs k0 => PDiamond jpc rs (rplan k0)
  | PRename m k0 => PRename (map (fun q => (rv (fst q), rv (snd q))) m) (rplan k0)
  | PCompact k0 => PCompact (rplan k0)
  | PVia j js lo karms k0 => PVia j (racs js) (rv lo) (rplan karms) (rplan k0)
  | PMerge j => PMerge j
  | PAbstractCell b n k0 => PAbstractCell (re b) n (rplan k0)
  | PHavocWords bs k0 => PHavocWords (map re bs) (rplan k0)
  | PRespell r e k0 => PRespell r (re e) (rplan k0)
  | PMmapInH a b c => PMmapInH (rplan a) (rplan b) (rplan c)
  end.
End Renum.


Fixpoint shift_atr8 (d : Z) (p : plan) : plan :=
  match p with
  | PSplit e m k1 k2 => if expr_eqb e e_atr8 then PSplit e (m + d) (shift_atr8 d k1) (shift_atr8 d k2)
                        else PSplit e m (shift_atr8 d k1) (shift_atr8 d k2)
  | PRun st k0 => PRun st (shift_atr8 d k0)
  | PCase2 e m k1 k2 => PCase2 e m (shift_atr8 d k1) (shift_atr8 d k2)
  | PFact K k0 => PFact K (shift_atr8 d k0)
  | PRespell r e k0 => PRespell r e (shift_atr8 d k0)
  | PBump m k0 => PBump m (shift_atr8 d k0)
  | PFresh r l b k0 => PFresh r l b (shift_atr8 d k0)
  | PX x a k0 => PX x a (shift_atr8 d k0)
  | PMmap a b => PMmap (shift_atr8 d a) (shift_atr8 d b)
  | PShDisj b1 n1 b2 n2 k0 => PShDisj b1 n1 b2 n2 (shift_atr8 d k0)
  | _ => p
  end.
Fixpoint shift_atr8_shape (d : Z) (s : shape) : shape :=
  match s with
  | SCase e m a b => if expr_eqb e e_atr8 then SCase e (m + d) (shift_atr8_shape d a) (shift_atr8_shape d b)
                     else SCase e m (shift_atr8_shape d a) (shift_atr8_shape d b)
  | SAlt2 a b => SAlt2 (shift_atr8_shape d a) (shift_atr8_shape d b)
  | _ => s
  end.
(* the AT_RANDOM shadow cases' move at (r = the rseq flag as 0 / 1) *)
Definition atr8_move (r : Z) : Z := 24 - (58 + 4 * r).
(* one r30q2 start-up plan / shape at *)
Definition plan727 (r : Z) (p : plan) : plan := shift_atr8 (atr8_move r) (rplan 15 4 p).
Definition shape727 (r : Z) (s : shape) : shape := shift_atr8_shape (atr8_move r) (rshape 15 4 s).
Definition nx727 (n : nat) : nat := rv 15 4 n.
