(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope bv_scope.
Local Notation psegs := Ubsan.M.loaded_segments.
Local Notation "# x" := (nan_box (low32 x)) (at level 9, format "# x").

Definition iir_yi (mem : list word) (x : word) : word := fadd_s RNE (# x) (# (hd w0 mem)).
Definition iir_nyi (mem : list word) (x : word) : word := fneg_s (iir_yi mem x).

Fixpoint iir_upd (nyi : word) (den mtl : list word) : list word :=
match den, mtl with
| d :: den', m1 :: mtl' => fmadd_s RNE (# d) nyi (# m1) :: iir_upd nyi den' mtl'
| _, _ => []
end.
Definition iir_mem' (den mem : list word) (x : word) : list word :=
iir_upd (iir_nyi mem x) den (tl mem) ++ [fmul_s RNE (# (last den w0)) (iir_nyi mem x)].
Fixpoint iir_st (den mem : list word) (xs : list word) : list word :=
match xs with [] => mem | x :: xs' => iir_st den (iir_mem' den mem x) xs' end.
Fixpoint iir_ys (den mem : list word) (xs : list word) : list word :=
match xs with [] => [] | x :: xs' => iir_yi mem x :: iir_ys den (iir_mem' den mem x) xs' end.

Lemma iir_st_app : forall den a b mem, iir_st den mem (a ++ b) = iir_st den (iir_st den mem a) b.
Proof. induction a; intros; cbn; [reflexivity| apply IHa]. Qed.
Lemma iir_ys_app : forall den a b mem, iir_ys den mem (a ++ b) = iir_ys den mem a ++ iir_ys den (iir_st den mem a) b.
Proof. induction a; intros; cbn; [reflexivity|]. now rewrite IHa. Qed.
Lemma length_iir_ys : forall den xs mem, length (iir_ys den mem xs) = length xs.
Proof. induction xs; intros; cbn; [reflexivity|]. now rewrite IHxs. Qed.
Lemma iir_upd_app : forall nyi a b c d, length a = length c ->
iir_upd nyi (a ++ b) (c ++ d) = iir_upd nyi a c ++ iir_upd nyi b d.
Proof. induction a as [|x a IH]; intros b [|z c] d L; cbn in *; try lia; [reflexivity|]. rewrite IH by lia. reflexivity. Qed.
Lemma iir_upd_trunc : forall nyi a b c, length c = length a -> iir_upd nyi (a ++ b) c = iir_upd nyi a c.
Proof. induction a as [|x a IH]; intros b [|z c] L; cbn in *; try lia. - destruct b; reflexivity. - rewrite IH by lia. reflexivity. Qed.
Lemma length_iir_upd : forall nyi a c, (length c <= length a)%nat -> length (iir_upd nyi a c) = length c.
Proof. induction a as [|x a IH]; intros [|z c] L; cbn in *; try lia. rewrite IH by lia. reflexivity. Qed.
Lemma length_iir_mem' : forall den mem x, length mem = length den -> (1 <= length den)%nat ->
length (iir_mem' den mem x) = length den.
Proof.
intros den mem x L L1. unfold iir_mem'. rewrite length_app, length_iir_upd; cbn [length].
- destruct mem; cbn in *; lia. - destruct mem; cbn in *; lia.
Qed.
Lemma length_iir_st : forall den xs mem, length mem = length den -> (1 <= length den)%nat -> length (iir_st den mem xs) = length den.
Proof. induction xs; intros; cbn; [assumption|]. apply IHxs; [apply length_iir_mem'; assumption| assumption]. Qed.
Lemma firstn_exact : forall {A} (l l' : list A), firstn (length l) (l ++ l') = l.
Proof. induction l; intros; cbn; [reflexivity|]. now rewrite IHl. Qed.
Lemma firstn_last : forall (l : list word), l <> [] -> firstn (length l - 1) l ++ [last l w0] = l.
Proof.
intros l Hl. destruct (exists_last Hl) as (l0 & a & ->). rewrite length_app. cbn [length].
replace (length l0 + 1 - 1)%nat with (length l0) by lia. rewrite firstn_exact, last_last. reflexivity.
Qed.
#[local] Hint Rewrite length_iir_ys : chunk_sizes.

Section S.
Context {RCEIL : RunCeiling}.
Variables (xs den mem : list word) (px pden py pm : Z).
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word.
Variables f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 : word.
Variable mi : word -> option byte.
Variable lo : Z.
Local Notation ord := (Z.of_nat (length den)).
Local Notation N := (Z.of_nat (length xs)).
Hypothesis LMEM : length mem = length den.
Hypothesis ORD : (2 <= ord < 2^31)%Z.
Hypothesis LEN : (1 <= N < 2^31)%Z.
Hypothesis SEPDM : (pden + 4 * ord <= pm \/ pm + 4 * ord <= pden)%Z.

Definition R (a2v a6v s7v s8v s9v s10v s11v : word) : bvmap 5 word :=
mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp (Z_to_bv 64 (ord + -1)) (Z_to_bv 64 (18446744073709551615 - pm))
(Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 px) (Z_to_bv 64 pden) a2v (Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 pm) a6v (Z_to_bv 64 1)
(Z_to_bv 64 1) (Z_to_bv 64 (4 * (ord - 1))) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (pm + 4)) s7v s8v s9v s10v s11v
(Z_to_bv 64 1) (Z_to_bv 64 (pden + 4 * (ord - 1))) (Z_to_bv 64 (pm + 4 * (ord - 1))) (Z_to_bv 64 1).
Definition FF (g12 g13 g14 g15 : word) : bvmap 5 word :=
mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 g12 g13 g14 g15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31.
Local Notation FRAME := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0].

Definition iir_inner_post (a2v a6v s7v : word) (memv : list word) (yi nyi : word) (m : word -> option byte)
: machine_state -> Prop :=
fun ms' => exists s8v s9v s10v s11v g12 g13 fc' m',
ms' = MS (R a2v a6v s7v s8v s9v s10v s11v) (FF g12 g13 nyi yi) (Z_to_bv 64 0x23410) fc' None m' (seg_rom psegs)
/\ munch [(pm, pm + 4 * ord)]%Z m m' /\ wmono psegs m m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' pden (f32 (firstn (length den - 1) den)) /\ rw_cells psegs m' (pden + 4 * (ord - 1))%Z [C4 (last den w0)]
/\ rw_cells psegs m' pm (f32 (iir_upd nyi den (tl memv))) /\ rw_cells psegs m' (pm + 4 * (ord - 1))%Z [C4 (last memv w0)].

Ltac inner_body o d c :=
zstep; zstep; if_false_z;
zstep; replace (pden + o)%Z with d by lia; zstep; if_false_z;
zstep; zstep; zstep; if_false_z; zstep; if_false_z;
zstep; replace (pm + 4 + o)%Z with (c + 4)%Z by lia;
zstep; zstep; zstep; replace (pm + o)%Z with c by lia;
zstep; zstep; zstep; zstep.

#[using="mem LMEM ORD SEPDM"] Lemma iir_inner : forall (a2v a6v s7v : word) (memv : list word) (yi nyi : word) (mI : word -> option byte)
mrest ddone (dj dj1 : word) drest tdone (mj mj1 : word) (o d c : Z) (s9v s10v s11v g12 g13 : word) fc m,
den = ddone ++ dj :: dj1 :: drest -> tl memv = tdone ++ mj1 :: mrest -> length memv = length den ->
length tdone = length ddone -> length drest = length mrest ->
o = (4 * Z.of_nat (length ddone))%Z -> d = (pden + o)%Z -> c = (pm + o)%Z -> (0 < pden)%Z ->
frm0 fc -> mem_inv psegs m -> munch [(pm, pm + 4 * ord)]%Z mI m -> wmono psegs mI m ->
rw_cells psegs m pden (f32 ddone) -> rw_cells psegs m d (f32 (dj :: dj1 :: drest)) ->
rw_cells psegs m pm (f32 (iir_upd nyi ddone tdone)) -> rw_cells psegs m c (f32 (mj :: mj1 :: mrest)) ->
evt psegs (iir_inner_post a2v a6v s7v memv yi nyi mI)
(MS (R a2v a6v s7v (Z_to_bv 64 o) s9v s10v s11v) (FF g12 g13 nyi yi) (Z_to_bv 64 0x233d0) fc None m (seg_rom psegs)).
Proof.
intros a2v a6v s7v memv yi nyi mI mrest.
induction mrest as [|mj2 mrest IH]; intros ddone dj dj1 drest tdone mj mj1 o d c s9v s10v s11v g12 g13 fc m
Hden Htl Lmv Ltd Ldr Ho Hd Hc PD FRM MI MU WM DDONE DCUR NEW MCUR;
pose proof (f_equal (@length word) Hden) as HL; rewrite length_app in HL; cbn [length] in HL;
pose proof (f_equal (@length word) Htl) as HT; rewrite length_app in HT; cbn [length] in HT;
assert (HT2 : length (tl memv) = (length memv - 1)%nat) by (destruct memv; cbn in *; lia);
pose proof (rw_cells_bound _ _ _ _ DCUR) as BD; rewrite cells_size_f32 in BD; cbn [length] in BD;
pose proof (rw_cells_bound _ _ _ _ MCUR) as BM; rewrite cells_size_f32 in BM; cbn [length] in BM;
pose proof (length_iir_upd nyi ddone tdone ltac:(lia)) as LNEW;
pose proof (rw_cells_bound _ _ _ _ NEW) as BN; rewrite cells_size_f32, LNEW in BN;
unfold R, FF; rewrite !f32_cons in DCUR; rewrite !f32_cons in MCUR.
-
destruct drest; [|cbn in Ldr; lia]. rewrite f32_nil in DCUR, MCUR.
inner_body o d c. if_false_x.
chunk_uncons MCUR as M1. chunk_snoc NEW M1. chunk_uncons DCUR as D1. chunk_snoc DDONE D1.
replace (c + 4)%Z with (pm + 4 * (ord - 1))%Z in MCUR by lia.
replace (d + 4)%Z with (pden + 4 * (ord - 1))%Z in DCUR by lia.
unfold iir_inner_post, R, FF. finish.
+ replace (firstn (length den - 1) den) with (ddone ++ [dj]).
2:{ replace (length den - 1)%nat with (length (ddone ++ [dj])) by (rewrite length_app; cbn; lia).
rewrite Hden. change (ddone ++ [dj; dj1]) with (ddone ++ ([dj] ++ [dj1])). rewrite app_assoc, firstn_exact. reflexivity. }
rewrite f32_app, f32_cons, f32_nil. exact DDONE.
+ replace (last den w0) with dj1.
2:{ rewrite Hden. change (ddone ++ [dj; dj1]) with (ddone ++ ([dj] ++ [dj1])). rewrite app_assoc, last_last. reflexivity. }
exact DCUR.
+ replace (iir_upd nyi den (tl memv)) with (iir_upd nyi ddone tdone ++ [fmadd_s RNE (# dj) nyi (# mj1)]).
2:{ rewrite Htl, Hden. change (ddone ++ [dj; dj1]) with (ddone ++ ([dj] ++ [dj1])).
rewrite app_assoc, iir_upd_trunc by (rewrite !length_app; cbn; lia).
rewrite iir_upd_app by lia. reflexivity. }
rewrite f32_app, f32_cons, f32_nil. exact NEW.
+ replace (last memv w0) with mj1.
2:{ destruct memv as [|m0' mtl]; [cbn in Lmv; lia|]. cbn [tl] in Htl. subst mtl. cbn [last].
destruct (tdone ++ [mj1]) eqn:E; [destruct tdone; discriminate|]. rewrite <- E. now rewrite last_last. }
exact MCUR.
-
destruct drest as [|dj2 drest]; [cbn in Ldr; lia|]. cbn [length] in Ldr, BD, BM. rewrite f32_cons in DCUR.
inner_body o d c. if_true_x.
chunk_uncons MCUR as M1. chunk_snoc NEW M1. chunk_uncons DCUR as D1. chunk_snoc DDONE D1.
apply (IH (ddone ++ [dj]) dj1 dj2 drest (tdone ++ [mj1]) mj1 mj2 (o + 4)%Z (d + 4)%Z (c + 4)%Z); try assumption;
first [ rewrite Hden, <- app_assoc; reflexivity
| rewrite Htl, <- app_assoc; reflexivity
| rewrite !length_app; cbn [length]; lia
| lia
| rewrite f32_app, f32_cons, f32_nil; exact DDONE
| rewrite !f32_cons; exact DCUR
| rewrite iir_upd_app, f32_app by lia; cbn [iir_upd]; rewrite f32_cons, f32_nil; exact NEW
| rewrite !f32_cons; exact MCUR ].
Qed.

Definition iir_post (W : list (Z * Z)) (inplace : bool) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a6 a7 t3 t4 t5 t6 g12 g13 g14 g15 fc' m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 (if inplace then px else py))
(Z_to_bv 64 N) (Z_to_bv 64 0) (Z_to_bv 64 pm) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(FF g12 g13 g14 g15) (ret_pc ra) fc' None m' (seg_rom psegs)
/\ munch W mi m' /\ wmono psegs mi m' /\ mem_inv psegs m'
/\ frm0 fc'
/\ rw_cells psegs m' (if inplace then px else py) (f32 (iir_ys den mem xs))
/\ rw_cells psegs m' pm (f32 (iir_st den mem xs))
/\ rw_cells psegs m' pden (f32 den)
/\ (inplace = false -> rw_cells psegs m' px (f32 xs))
/\ stk psegs m' lo (bv_unsigned sp).

Local Notation WI := ([(lo, bv_unsigned sp); (px, px + 4 * N); (pm, pm + 4 * ord)]%Z).
Local Notation WD := ([(lo, bv_unsigned sp); (py, py + 4 * N); (pm, pm + 4 * ord)]%Z).

Ltac outer_pre i q :=
zstep; replace (Z.shiftl i 2) with (4 * i)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia);
zstep; replace (px + 4 * i)%Z with q by lia;
zstep; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; zstep; zstep; zstep; if_false_x; zstep.

Ltac outer_post a q :=
zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; replace a with q by lia;
zstep; zstep; zstep; zstep; if_false_z; zstep; if_false_z; zstep; if_false_z;
zstep; zstep; zstep.

Ltac frame_exit := do 12 zstep; zstep; zstep.

#[using="LMEM ORD LEN SEPDM"] Lemma iir_outer_ip : forall rest done x memv (i q : Z) (s7v s8v s9v s10v s11v g12 g13 g14 g15 : word) fc m,
(px + 4 * N <= pm \/ pm + 4 * ord <= px)%Z -> (px + 4 * N <= pden \/ pden + 4 * ord <= px)%Z ->
(lo + 96 <= bv_unsigned sp)%Z -> (px + 4 * N <= lo \/ bv_unsigned sp <= px)%Z ->
(pden + 4 * ord <= lo \/ bv_unsigned sp <= pden)%Z -> (pm + 4 * ord <= lo \/ bv_unsigned sp <= pm)%Z ->
(0 < px)%Z -> (0 < pden)%Z ->
xs = done ++ x :: rest -> i = Z.of_nat (length done) -> memv = iir_st den mem done -> q = (px + 4 * i)%Z ->
frm0 fc -> mem_inv psegs m -> munch WI mi m -> wmono psegs mi m ->
stk psegs m lo (bv_unsigned sp + -96) -> rw_cells psegs m (bv_unsigned sp + -96) FRAME ->
rw_cells psegs m px (f32 (iir_ys den mem done)) -> rw_cells psegs m q (f32 (x :: rest)) ->
rw_cells psegs m pm (f32 memv) -> rw_cells psegs m pden (f32 den) ->
evt psegs (iir_post WI true)
(MS (R (Z_to_bv 64 px) (Z_to_bv 64 i) s7v s8v s9v s10v s11v) (FF g12 g13 g14 g15) (Z_to_bv 64 0x2339c) fc None m (seg_rom psegs)).
Proof.
induction rest as [|x' rest IH]; intros done x memv i q s7v s8v s9v s10v s11v g12 g13 g14 g15 fc m SEPXM SEPXD LOW AXS ADS AMS PX0 PD0
Hxs Hi Hmv Hq FRM MI MU WM ST FR DONE X MEM DEN;
pose proof (f_equal (@length word) Hxs) as HL; rewrite length_app in HL; cbn [length] in HL;
assert (Lmv : length memv = length den) by (subst memv; apply length_iir_st; [exact LMEM| lia]);
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, Lmv in BM;
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ DONE) as BDO; rewrite cells_size_f32, length_iir_ys in BDO;
pose proof (rw_cells_bound _ _ _ _ FR) as BFR; cbn [cells_size csize Nat.add] in BFR;
destruct memv as [|mv0 mvt] eqn:Emv; try (cbn in Lmv; lia); rewrite <- Emv in *;
destruct den as [|de0 [|de1 det]] eqn:Eden; try (cbn in ORD; lia); rewrite <- Eden in *;
destruct mvt as [|mv1 mvtt] eqn:Emvt; try (subst; cbn in Lmv; lia); rewrite <- Emvt in *;
rewrite !f32_cons in X; rewrite Emv, f32_cons in MEM; unfold R, FF.
- outer_pre i q.
rewrite Emvt in MEM. rewrite Eden in DEN.
assert (Ldm : length det = length mvtt) by (clear - Lmv Emv Emvt Eden; rewrite Emv, Emvt, Eden in Lmv; cbn in Lmv; lia).
assert (Htl : tl memv = [] ++ mv1 :: mvtt) by (rewrite Emv, Emvt; reflexivity).
assert (D0 : rw_cells psegs m pden (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia).
assert (M0 : rw_cells psegs m pm (f32 (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) [] []))) by (cbn [iir_upd]; rewrite f32_nil; apply rw_cells_nil; lia).
pose proof (munch_refl [(pm, pm + 4 * ord)]%Z m) as MU0. pose proof (wmono_refl psegs m) as WM0.
call (iir_inner (Z_to_bv 64 px) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) memv _ _ m mvtt [] de0 de1 det [] mv0 mv1 0 pden pm);
[ exact Eden | exact Htl | exact Lmv | reflexivity | exact Ldm | reflexivity | lia | lia | exact PD0
| exact FRM | exact MI | exact MU0 | exact WM0 | exact D0 | exact DEN | exact M0 | exact MEM | ].
clear Ldm Htl; try clear D0; try clear M0; try clear MU0; try clear WM0. unfold R, FF.
match goal with H : rw_cells _ _ (pden + 4 * (ord - 1))%Z _ |- _ => rename H into DL end.
match goal with H : rw_cells _ _ (pm + 4 * (ord - 1))%Z _ |- _ => rename H into ML end.
match goal with H : rw_cells _ _ pden (f32 (firstn _ _)) |- _ => rename H into DP end.
match goal with H : rw_cells _ _ pm (f32 (iir_upd _ _ _)) |- _ => rename H into MP end.
pose proof (rw_cells_bound _ _ _ _ DL) as BDL; pose proof (rw_cells_bound _ _ _ _ ML) as BML; cbn [cells_size csize Nat.add] in BDL, BML.
assert (LUP : length (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) den (tl memv)) = (length den - 1)%nat)
by (rewrite length_iir_upd; rewrite Emv; cbn [tl]; subst; cbn in *; lia).
pose proof (firstn_length_le den (n := (length den - 1)%nat) ltac:(lia)) as LFD.
remember (pden + 4 * (ord - 1))%Z as dl eqn:Hdl in *. remember (pm + 4 * (ord - 1))%Z as ml eqn:Hml in *.
outer_post (px + 4 * i)%Z q.
if_false_x.
frame_exit.
release_frame FR ST (bv_unsigned sp).

chunk_snoc DP DL. replace (f32 (firstn (length den - 1) den) ++ [C4 (last den w0)]) with (f32 den) in DP
by (rewrite <- (firstn_last den) at 1 by (rewrite Eden; discriminate); rewrite f32_app, f32_cons, f32_nil; reflexivity).
chunk_snoc MP ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MP.
rewrite f32_nil in X. chunk_snoc DONE X. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
unfold iir_post. finish.
+ rewrite Hxs, iir_ys_app. cbn [iir_ys]. rewrite <- Hmv. unfold iir_yi. rewrite Emv. cbn [hd]. exact DONE.
+ rewrite Hxs, iir_st_app. cbn [iir_st]. rewrite <- Hmv. unfold iir_mem', iir_nyi, iir_yi. rewrite Emv in MP |- *. cbn [hd tl] in MP |- *. exact MP.
+ intros; discriminate.
-
cbn [length] in HL, BX.
outer_pre i q.
rewrite Emvt in MEM. rewrite Eden in DEN.
assert (Ldm : length det = length mvtt) by (clear - Lmv Emv Emvt Eden; rewrite Emv, Emvt, Eden in Lmv; cbn in Lmv; lia).
assert (Htl : tl memv = [] ++ mv1 :: mvtt) by (rewrite Emv, Emvt; reflexivity).
assert (D0 : rw_cells psegs m pden (f32 [])) by (rewrite f32_nil; apply rw_cells_nil; lia).
assert (M0 : rw_cells psegs m pm (f32 (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) [] []))) by (cbn [iir_upd]; rewrite f32_nil; apply rw_cells_nil; lia).
pose proof (munch_refl [(pm, pm + 4 * ord)]%Z m) as MU0. pose proof (wmono_refl psegs m) as WM0.
call (iir_inner (Z_to_bv 64 px) (Z_to_bv 64 i) (Z_to_bv 64 (4 * i)) memv _ _ m mvtt [] de0 de1 det [] mv0 mv1 0 pden pm);
[ exact Eden | exact Htl | exact Lmv | reflexivity | exact Ldm | reflexivity | lia | lia | exact PD0
| exact FRM | exact MI | exact MU0 | exact WM0 | exact D0 | exact DEN | exact M0 | exact MEM | ].
clear Ldm Htl; try clear D0; try clear M0; try clear MU0; try clear WM0. unfold R, FF.
match goal with H : rw_cells _ _ (pden + 4 * (ord - 1))%Z _ |- _ => rename H into DL end.
match goal with H : rw_cells _ _ (pm + 4 * (ord - 1))%Z _ |- _ => rename H into ML end.
match goal with H : rw_cells _ _ pden (f32 (firstn _ _)) |- _ => rename H into DP end.
match goal with H : rw_cells _ _ pm (f32 (iir_upd _ _ _)) |- _ => rename H into MP end.
pose proof (rw_cells_bound _ _ _ _ DL) as BDL; pose proof (rw_cells_bound _ _ _ _ ML) as BML; cbn [cells_size csize Nat.add] in BDL, BML.
assert (LUP : length (iir_upd (fneg_s (fadd_s RNE (# x) (# mv0))) den (tl memv)) = (length den - 1)%nat)
by (rewrite length_iir_upd; rewrite Emv; cbn [tl]; subst; cbn in *; lia).
pose proof (firstn_length_le den (n := (length den - 1)%nat) ltac:(lia)) as LFD.
remember (pden + 4 * (ord - 1))%Z as dl eqn:Hdl in *. remember (pm + 4 * (ord - 1))%Z as ml eqn:Hml in *.
outer_post (px + 4 * i)%Z q.
if_true_x.
chunk_snoc DP DL. replace (f32 (firstn (length den - 1) den) ++ [C4 (last den w0)]) with (f32 den) in DP
by (rewrite <- (firstn_last den) at 1 by (rewrite Eden; discriminate); rewrite f32_app, f32_cons, f32_nil; reflexivity).
chunk_snoc MP ML. rewrite <- f32_nil, <- f32_cons, <- f32_app in MP.
chunk_uncons X as X1. chunk_snoc DONE X1. rewrite <- f32_nil, <- f32_cons, <- f32_app in DONE.
subst dl ml.

eapply (IH (done ++ [x]) x' (iir_mem' den memv x) (i + 1)%Z (q + 4)%Z);
[ exact SEPXM | exact SEPXD | exact LOW | exact AXS | exact ADS | exact AMS | exact PX0 | exact PD0
| rewrite Hxs, <- app_assoc; reflexivity
| rewrite length_app; cbn [length]; lia
| rewrite iir_st_app; cbn [iir_st]; rewrite <- Hmv; reflexivity
| lia
| eassumption | eassumption | exact MU | exact WM | exact ST | exact FR
| rewrite iir_ys_app; cbn [iir_ys]; rewrite <- Hmv; unfold iir_yi; rewrite Emv; cbn [hd]; exact DONE
| exact X
| unfold iir_mem', iir_nyi, iir_yi; rewrite Emv in MP |- *; cbn [hd tl] in MP |- *; exact MP
| exact DP ].
Qed.

Ltac iir_prologue :=
zstep; do 12 zstep; zstep; if_false_x; do 42 zstep;
rewrite (swrap32_small (ord + -1)) by lia;
rewrite (Z.mod_small (ord + -1) 18446744073709551616) by lia;
replace (Z.shiftl (ord + -1) 2) with (4 * (ord - 1))%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia);
rewrite (Z.mod_small (pden + 4 * (ord - 1)) 18446744073709551616) by lia;
rewrite (Z.mod_small (pm + 4 * (ord - 1)) 18446744073709551616) by lia;
replace (Z.lxor (ord + -1) 9223372036854775808) with (ord + -1 + 9223372036854775808)%Z
by (change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity);
replace (Z.lxor ord 9223372036854775808) with (ord + 9223372036854775808)%Z
by (change 9223372036854775808%Z with (2^63)%Z; rewrite zb_lxor_sign by lia; rewrite Z.mod_small by lia; reflexivity);
rewrite (zb_lxor_ones pm) by lia.

#[using="LMEM ORD LEN SEPDM"] Lemma iir_mem16_spec_inplace : forall t0 t1 t2 a6 a7 t3 t4 t5 t6 fc,
(px + 4 * N <= pm \/ pm + 4 * ord <= px)%Z -> (px + 4 * N <= pden \/ pden + 4 * ord <= px)%Z ->
rw_cells psegs mi px (f32 xs) -> rw_cells psegs mi pm (f32 mem) -> rw_cells psegs mi pden (f32 den) ->
mem_inv psegs mi -> frm0 fc ->
stk psegs mi lo (bv_unsigned sp) -> (lo + 96 <= bv_unsigned sp)%Z ->
(px + 4 * N <= lo \/ bv_unsigned sp <= px)%Z -> (pden + 4 * ord <= lo \/ bv_unsigned sp <= pden)%Z ->
(pm + 4 * ord <= lo \/ bv_unsigned sp <= pm)%Z ->
(0 < px)%Z -> (px mod 4 = 0)%Z -> (0 < pden)%Z -> (pden mod 4 = 0)%Z -> (0 < pm)%Z -> (pm mod 4 = 0)%Z ->
evt psegs (iir_post WI true)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 px) (Z_to_bv 64 pden) (Z_to_bv 64 px) (Z_to_bv 64 N) (Z_to_bv 64 ord) (Z_to_bv 64 pm) a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(mkF f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31)
(Z_to_bv 64 0x232bc) fc None mi (seg_rom psegs)).
Proof.
intros t0 t1 t2 a6 a7 t3 t4 t5 t6 fc SEPXM SEPXD X MEM DEN MI FRM ST LOW AXS ADS AMS PX0 PX4 PD0 PD4 PM0 PM4.
pose proof (rw_cells_bound _ _ _ _ X) as BX; rewrite cells_size_f32 in BX.
pose proof (rw_cells_bound _ _ _ _ MEM) as BM; rewrite cells_size_f32, LMEM in BM.
pose proof (rw_cells_bound _ _ _ _ DEN) as BD; rewrite cells_size_f32 in BD.
pose proof (munch_refl WI mi) as MU. pose proof (wmono_refl psegs mi) as WM.
destruct xs as [|x rest] eqn:Exs; [cbn in LEN; lia|]. rewrite <- Exs in *.
carve_frame 96%nat ST.
iir_prologue.
replace (Z.land (Z.lor px pm) 3) with 0%Z
by (rewrite Z.land_lor_distr_l; change 3%Z with (Z.ones 2); rewrite !Z.land_ones by lia; change (2^2)%Z with 4%Z; rewrite PX4, PM4; reflexivity).
cond_prep.
replace (Z.shiftl (Z.land 18446744073709551615 (ord + -1)) 2) with (4 * (ord - 1))%Z
by (change 18446744073709551615%Z with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by lia;
rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
rewrite Exs in X.
eapply (iir_outer_ip rest [] x mem 0%Z px);
[ exact SEPXM | exact SEPXD | exact LOW | exact AXS | exact ADS | exact AMS | exact PX0 | exact PD0
| exact Exs | reflexivity | reflexivity | lia
| exact FRM | exact MI | exact MU | exact WM | exact ST | exact FR
| cbn [iir_ys]; rewrite f32_nil; apply rw_cells_nil; lia
| exact X | exact MEM | exact DEN ].
Qed.
End S.
