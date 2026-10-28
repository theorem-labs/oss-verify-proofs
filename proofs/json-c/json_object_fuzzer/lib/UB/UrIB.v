(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7 QJjn QKQo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI Uu4M Uihm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhI1 UunB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qvbw QYIF Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg QWxq.Mq0.
Import UEQM.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ.
Import UC8c.Mq0.
Import Qsw7 QJjn QKQo.
Import UPZI.Mq0 Uu4M.Mq0 Uihm.
Import QSL3.
Import UhI1.
Import UunB.
Import Qvbw QYIF.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma nodup_mid_notin : forall (X Y W : list blk) a n k,
List.NoDup (map blk_addr (X ++ Y ++ W)) -> In (a, n) Y -> ~ In (a, k) (X ++ W).
Proof.
intros X Y W a n k ND HY HIN. apply in_split in HY as (Y1 & Y2 & ->).
rewrite !map_app in ND. cbn [map] in ND. rewrite <- (app_assoc (map blk_addr Y1)) in ND. cbn [app] in ND.
rewrite (app_assoc (map blk_addr X)) in ND.
apply NoDup_remove_2 in ND. apply ND. cbn [blk_addr].
apply in_app_or in HIN as [H|H]; [apply in_or_app; left; apply in_or_app; left | apply in_or_app; right; apply in_or_app; right]; exact (in_map blk_addr _ _ H).
Qed.
End RC__1.

Ltac in_find Hb := first [ exact Hb | apply in_or_app; first [ left; in_find Hb | right; in_find Hb ] | right; in_find Hb | left; reflexivity ].
Ltac incl_tac := let b := fresh "b" in let Hb := fresh "Hb" in intros b Hb; repeat (apply in_app_or in Hb; destruct Hb as [Hb|Hb]); in_find Hb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section Gen.
Variable L : heap_layout.
Variable fn : fnaddrs.
Notation segs := (hl_segs L).
Notation rw_cells := (rw_cells (hl_segs L)).
Notation bytes_at := (bytes_at (hl_segs L)).

Definition scopy (r : jroot) (m : word -> option byte) (CBS : list blk) (q : Z) : Prop :=
match r with
| JRnull => False
| JRtree (Sdouble true) =>
CBS = [(q, 48)] /\ exists bits : word, rw_cells m q (jhdr_cells JT_DOUBLE 1 (fn_ud_to_json_string fn) 0 0 0 ++ [C8 bits])
| JRtree (Sstr _) | JRstrx => jval segs fn (Sstr false) m CBS q 1
| JRtree (Sobj _) => jval segs fn (Sobj []) m CBS q 1
| JRtree (Sarr _) => jval segs fn (Sarr []) m CBS q 1
| JRtree s => jval segs fn s m CBS q 1
| JRdblx tojs => CBS = [(q, 48)] /\ xdbl L m CBS q 1 tojs
end.

#[using="Type"] Lemma xdbl_agree : forall m m' BS BS' p rc tojs,
xdbl L m BS p rc tojs -> agree_on segs BS' m m' -> incl BS BS' -> xdbl L m' BS p rc tojs.
Proof.
intros m m' BS BS' p rc tojs (pb & PBS & bits & -> & OPB & H) AG INCL. exists pb, PBS, bits. split; [reflexivity|]. split.
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply INCL; right; exact Hb].
- eapply rw_cells_agree; [exact H | exact AG | exists p, 48; split; [apply INCL; left; reflexivity | cbn; lia]].
Qed.

#[using="Type"] Lemma xstr_agree : forall m m' BS BS' p rc,
xstr L fn m BS p rc -> agree_on segs BS' m m' -> incl BS BS' -> xstr L fn m' BS p rc.
Proof.
intros m m' BS BS' p rc (pb & PBS & DBS & cap & len & str & -> & OPB & Hcap & Hlen & Hstr & ALT) AG INCL.
exists pb, PBS, DBS, cap, len, str. split; [reflexivity|]. split.
{ eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; apply INCL; right; apply in_or_app; right; exact Hb]. }
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hstr|].
destruct ALT as [(H0 & -> & H1 & junk & H) | (H0 & pd & pdn & junk & junk2 & -> & H1 & H & HD)].
- left. split; [exact H0|]. split; [reflexivity|]. split; [exact H1|]. exists junk.
eapply rw_cells_agree; [exact H | exact AG |]. exists p, (48 + cap). split; [apply INCL; left; reflexivity|].
cbn [cells_size csize jhdr_cells app Nat.add]. lia.
- right. split; [exact H0|]. exists pd, pdn, junk, junk2. split; [reflexivity|]. split; [exact H1|]. split.
+ eapply rw_cells_agree; [exact H | exact AG |]. exists p, (48 + cap). split; [apply INCL; left; reflexivity|].
cbn [cells_size csize jhdr_cells app Nat.add]. lia.
+ eapply rw_cells_agree; [exact HD | exact AG |]. exists pd, pdn. split; [apply INCL; right; left; reflexivity|]. cbn. lia.
Qed.

#[using="Type"] Lemma jroot_rep_agree : forall r m m' BS BS' p,
jroot_rep L fn r m BS p -> agree_on segs BS' m m' -> incl BS BS' -> jroot_rep L fn r m' BS p.
Proof.
intros r m m' BS BS' p H AG INCL. destruct r as [|s|tojs|]; cbn in H |- *.
- exact H.
- destruct H as [Hp J]. split; [exact Hp|]. eapply jval_agree; [exact J | exact AG | exact INCL].
- destruct H as (Hp & Ht & X). split; [exact Hp|]. split; [exact Ht|]. eapply xdbl_agree; eassumption.
- destruct H as [Hp X]. split; [exact Hp|]. eapply xstr_agree; eassumption.
Qed.

#[using="Type"] Lemma jroot_rep_root_in : forall r m BS p, jroot_rep L fn r m BS p -> r <> JRnull -> exists n, In (p, n) BS /\ 48 <= n.
Proof.
intros r m BS p H NN. destruct r as [|s|tojs|]; cbn in H.
- exfalso. apply NN. reflexivity.
- destruct H as [_ J]. exact (jval_root_in segs fn _ _ _ _ _ J).
- destruct H as (_ & _ & pb & PBS & bits & -> & _). exists 48. split; [left; reflexivity | lia].
- destruct H as (_ & pb & PBS & DBS & cap & len & str & -> & _ & Hcap & _). exists (48 + cap). split; [left; reflexivity | lia].
Qed.

#[using="Type"] Lemma presxD_trans : forall D LB SP m1 m2 m3,
heap_presxD L D LB SP m1 m2 -> heap_presxD L D LB SP m2 m3 -> heap_presxD L D LB SP m1 m3.
Proof.
intros D LB SP m1 m2 m3 H1 H2 a Ha Hc Hd. destruct (H1 a Ha Hc Hd) as [E1 W1]. destruct (H2 a Ha Hc Hd) as [E2 W2].
split; [congruence | auto].
Qed.

#[using="Type"] Lemma presx_presxD : forall D LB SP m m',
heap_presx L (hl_volatile L) LB SP m m' -> heap_presxD L D LB SP m m'.
Proof. intros D LB SP m m' H a Ha Hc _. exact (H a Ha Hc). Qed.

#[using="Type"] Lemma pres_presxD : forall D LB SP m m',
heap_pres L LB SP m m' -> heap_presxD L D LB SP m m'.
Proof. intros D LB SP m m' H. apply presx_presxD. apply heap_pres_presx. exact H. Qed.

#[using="Type"] Lemma presxD_weaken : forall D LB LB' SP SP' m m',
heap_presxD L D LB SP m m' -> SP <= SP' -> incl LB' LB -> heap_presxD L D LB' SP' m m'.
Proof.
intros D LB LB' SP SP' m m' H HS HL a Ha Hc Hd. apply H; [exact Ha | | exact Hd].
unfold client_addrx, in_block in *.
destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia | right; left; exact Hc | right; right].
exists b. split; [apply HL; exact Hb | exact Hr].
Qed.

#[using="Type"] Lemma presxD_presx : forall (HIx : heap_iface L) A LBall mx md D' LB SP SP' m m',
heap_presxD L D' LB SP m m' -> HEAP L HIx A LBall mx md -> incl LB LBall ->
SP <= SP' -> D' + 8 <= SP' -> alloc_ceiling <= D' ->
heap_presx L (hl_volatile L) LB SP' m m'.
Proof.
intros HIx A LBall mx md D' LB SP SP' m m' H HP INCL HS HD HC a Ha Hc. apply H; [exact Ha | |].
- unfold client_addrx, in_block in *. destruct Hc as [Hc|[Hc|Hc]]; [left; lia | right; left; exact Hc | right; right; exact Hc].
- intros Hin. unfold client_addrx in Hc. destruct Hc as [Hc|[[Hc _]|(b & Hb & Hr)]]; [lia | |].
+ pose proof (hl_static_in_img L a Hc). pose proof (hl_img_range L). lia.
+ destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk L HIx _ _ _ _ ba bn HP (INCL _ Hb)) as (_ & _ & _ & Hhi & _). lia.
Qed.

#[using="Type"] Lemma presxD_rw_cells : forall D LB SP m m' A cs,
heap_presxD L D LB SP m m' -> rw_cells m A cs ->
client_rangex L (hl_volatile L) LB SP A (Z.of_nat (cells_size cs)) ->
(A + Z.of_nat (cells_size cs) <= D \/ D + 8 <= A) ->
rw_cells m' A cs.
Proof.
intros D LB SP m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
- destruct HB as (H0 & H1 & HB'). split; [exact H0|]. split; [exact H1|].
rewrite cells_bytes_length in H1, HB' |- * by assumption.
intros i Hi. rewrite <- (HB' i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_rangex_addr; [exact HR|lia]) ltac:(lia)) as [E _].
rewrite E. reflexivity.
- destruct HW as (H0 & H1 & HW'). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(eapply client_rangex_addr; [exact HR|lia]) ltac:(lia)) as [_ W].
apply W. apply HW'. exact Hi.
Qed.

#[using="Type"] Lemma presxD_bytes_at : forall D LB SP m m' A bs,
heap_presxD L D LB SP m m' -> bytes_at m A bs ->
client_rangex L (hl_volatile L) LB SP A (Z.of_nat (length bs)) ->
(A + Z.of_nat (length bs) <= D \/ D + 8 <= A) ->
bytes_at m' A bs.
Proof.
intros D LB SP m m' A bs HP (H0 & H1 & HB) HR HD. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply client_rangex_addr; [exact HR|lia]) ltac:(lia)) as [E _].
rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma presxD_agree : forall (HIx : heap_iface L) A LBall mx md D LB SP m m' BS,
heap_presxD L D LB SP m m' -> HEAP L HIx A LBall mx md -> incl BS LB -> incl LB LBall -> alloc_ceiling <= D ->
agree_on segs BS m m'.
Proof.
intros HIx A LBall mx md D LB SP m m' BS HP HH I1 I2 HC a Ha (b & Hb & Hr). apply HP; [exact Ha | |].
- right; right. exists b. split; [apply I1; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn in Hr. pose proof (heap_blk L HIx _ _ _ _ ba bn HH (I2 _ (I1 _ Hb))) as (_ & _ & _ & Hhi & _). lia.
Qed.

#[using="Type"] Lemma presxD_of_munch : forall D LB SP W m m',
munch W m m' -> wmono segs m m' ->
(forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> ~ (D <= a < D + 8) -> outside W a) ->
heap_presxD L D LB SP m m'.
Proof.
intros D LB SP W m m' MU WM HW a Ha Hc Hd. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; [exact Ha | exact (client_addrx_addr L _ _ _ _ Hc) | exact Hd].
- apply WM.
Qed.

#[using="Type"] Lemma client_outsideD : forall (HIx : heap_iface L) A LBc LB0 m md W SP D0,
HEAP L HIx A LBc m md -> (forall b, In b LB0 -> In b LBc) -> alloc_ceiling <= SP ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP)
\/ (exists a n, In (a, n) LBc /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch L x)) W ->
forall a, 0 <= a < 2^64 -> client_addr L LB0 SP a -> ~ (D0 <= a < D0 + 8) -> outside ((D0, D0 + 8) :: W) a.
Proof. intros. cbn [outside]. split; [assumption | eapply (client_outside L HIx); eauto]. Qed.

Definition fsv8 (F F' : bvmap 5 word) : Prop :=
forall k, In k FSAVED -> k <> 8 -> Sem.reg_get F' (Z_to_bv 5 k) = Sem.reg_get F (Z_to_bv 5 k).
#[using="Type"] Lemma fsv8_refl : forall F, fsv8 F F. Proof. intros F k _ _; reflexivity. Qed.
#[using="Type"] Lemma fsv8_of_fsaved : forall F F', fsaved F F' -> fsv8 F F'. Proof. intros F F' H k Hk _. apply H. exact Hk. Qed.

#[using="Type"] Lemma fsaved_ix : forall j, In j FSAVED -> bv_unsigned (Z_to_bv 5 j) = j.
Proof. intros j Hj. unfold FSAVED in Hj. cbn in Hj. intuition (subst; reflexivity). Qed.
#[using="Type"] Lemma fsv8_set8 : forall F F' (k8 : bv 5) v, bv_unsigned k8 = 8 -> fsv8 F F' -> fsv8 F (bvmap_set k8 v F').
Proof.
intros F F' k8 v E H k Hk NE. rewrite QEpW.reg_get_set_other; [apply H; assumption|].
intros E2. apply NE. rewrite <- (fsaved_ix k Hk), <- E2. exact E.
Qed.
#[using="Type"] Lemma fsv8_restore : forall F F' (k1 k2 : bv 5), bv_unsigned k1 = 8 -> bv_unsigned k2 = 8 ->
fsv8 F F' -> fsaved F (bvmap_set k1 (Sem.reg_get F k2) F').
Proof.
intros F F' k1 k2 E1 E2 H j Hj.
replace k2 with k1 by (apply bv_eq; lia).
destruct (Z.eq_dec j 8) as [->|NE].
- replace (Z_to_bv 5 8) with k1 by (apply bv_eq; rewrite E1; reflexivity). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other; [apply H; assumption|]. intros E. apply NE. rewrite <- (fsaved_ix j Hj), <- E. exact E1.
Qed.

End Gen.

Section Stmt.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable G : (word -> option byte) -> Prop.
Notation segs := (hl_segs L).

Definition shallow_res (r : jroot) (BS LB : list blk) (D : Z) (m' : word -> option byte) (md' : Model) (rv : Z) : Prop :=
(rv = 1 /\ exists (A' : AS L HIx) q CBS, q <> 0 /\ rw_cells segs m' D [C8 (Z_to_bv 64 q)] /\
scopy L fn r m' CBS q /\ HEAP L HIx A' (BS ++ CBS ++ LB) m' md')
\/ (rv = 2^64 - 1 /\ exists (A' : AS L HIx), rw_cells segs m' D [C8 (Z_to_bv 64 0)] /\ HEAP L HIx A' (BS ++ LB) m' md').

Definition shallow_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB BS : list blk) (lo p D : Z) (dold : word) (r : jroot) (errv : word),
HEAP L HIx A (BS ++ LB) m md -> jroot_rep L fn r m BS p -> r <> JRnull -> G m ->
rw_cells segs m D [C8 dold] -> bv_unsigned sp <= D -> D + 8 <= hi_top L HIx -> D mod 8 = 0 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - stkb ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top L HIx ->
rw_cells segs m (hl_tp L - 164) [C4 errv] -> tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p -> a4 = Z_to_bv 64 D ->
(forall ms' md' m' rv,
jf_postD L D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) lo rv m' ms' md' ->
G m' -> jroot_rep L fn r m' BS p -> shallow_res r BS LB D m' md' rv ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.
End Stmt.

Definition SH_ENTRY_P : Z := 0x26968.
Definition SH_STK_P : Z := 64 + 48 + 48 + 8256.
Definition SH_JOIN_P : Z := 0x26c2c.
End RC__2.

Ltac step_until pc :=
repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | |- _ => bstep end).

Ltac extend_presD L HIx PRES MU WM HPc :=
lazymatch type of PRES with heap_presxD _ ?Dx ?LB0 ?SP ?me ?ma =>
lazymatch type of MU with munch _ _ ?mb =>
let H := fresh "HPRx" in
assert (H : heap_presxD L Dx LB0 SP me mb);
[ eapply presxD_trans; [exact PRES|]; apply pres_presxD;
eapply (heap_pres_of_munch L LB0 SP); [exact MU | exact WM |];
eapply (client_outside L HIx); [exact HPc | incl_tac | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia | solve_clientW L HIx HPc]
| clear PRES; rename H into PRES ] end end.

Ltac extend_presD_call PRES HPR2 :=
lazymatch type of PRES with heap_presxD ?L ?Dx ?LB0 ?SP ?me ?ma =>
lazymatch type of HPR2 with
| heap_pres _ _ _ _ ?mb =>
let H := fresh "HPRx" in
assert (H : heap_presxD L Dx LB0 SP me mb);
[ eapply presxD_trans; [exact PRES|]; apply pres_presxD;
eapply heap_pres_weaken; [exact HPR2 | lia | incl_tac]
| clear PRES; rename H into PRES ]
| heap_presx _ _ _ _ _ ?mb =>
let H := fresh "HPRx" in
assert (H : heap_presxD L Dx LB0 SP me mb);
[ eapply presxD_trans; [exact PRES|]; apply presx_presxD;
eapply heap_presx_weaken; [exact HPR2 | lia | incl_tac | intros ? Xa; exact Xa]
| clear PRES; rename H into PRES ]
end end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__3. Context {RC__ : Q6q3.RunConsts}.

Section ShallowP.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Notation wz := (Z_to_bv 64).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB BS : list blk) (lo p D : Z) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_P.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hi_top S4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis SPD : bv_unsigned sp <= D.
Hypothesis DHI : D + 8 <= hi_top S4L HIx.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.

Hypothesis JR0 : jroot_rep S4L S4F r m0 BS p.
Hypothesis Kont : forall ms' md' m' rv,
jf_postD S4L D ra sp gp (wz 0x77c00) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) lo rv m' ms' md' ->
jc_glob_P m' -> jroot_rep S4L S4F r m' BS p -> shallow_res S4L HIx S4F r BS LB D m' md' rv ->
realizes rsegs (mkCfg ms' md') T.

Definition sh_frame (m : word -> option byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -64) [C8 (Sem.reg_get F (Z_to_bv 5 8)); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sh_inv (mc : word -> option byte) (mdc : Model) : Prop :=
model_vm_only md0 mdc /\ heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) m0 mc /\
stk rsegs mc lo (bv_unsigned sp + -64) /\ sh_frame mc /\ jc_glob_P mc.

#[using="LO LOS SPA RA SPD DHI DAL NN JR0 Kont"] Lemma sh_join38 :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (q ty tojs : Z) (dold errc : word),
sh_inv mc mdc -> fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc (p + 8) [C8 (wz tojs)] ->
( (q = 0 /\ exists A', HEAPx A' (BS ++ LB) mc mdc)
\/ (q <> 0 /\ exists A' CBS nq tojs0, HEAPx A' (BS ++ CBS ++ LB) mc mdc /\ In (q, nq) CBS /\ 16 <= nq /\
rw_cells rsegs mc q [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] /\
(forall m', rw_cells rsegs m' q [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ->
munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono rsegs mc m' -> scopy S4L S4F r m' CBS q)) ) ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) (wz q) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26c38) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros (VM & PRES & ST & FR & G) FS FRM DC ERR SRC8 NODE.
unfold sh_frame in FR. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (HD0 : 0 < D < 2^64) by (first [pose proof (rw_cells_bound _ _ _ _ DC) as HB | pose proof (rw_cells_bound _ _ _ DC) as HB]; cbn in HB; lia).
destruct (jroot_rep_root_in S4L S4F r m0 BS p JR0 NN) as (np & INp & Hnp).
destruct NODE as [(-> & A1 & HP) | (Hq & A1 & CBS & nq & tojs0 & HP & INq & Hnq & QH & CLOSE)].
-
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (490332, 490336)] mc) as MU.
stash G.
apply rz_evt; [exact MOK|].
bstepz. bstep. if_true. bstep. bstep. bstep. bstep. bstep. bstepz. bstep.
do 10 bstep.
apply evt_RZ_done. unstash G.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) mc mj).
{ eapply presxD_of_munch; [exact MU | exact WM |].
eapply (client_outsideD S4L HIx); [exact HP | incl_tac | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. intros; simpl hl_scratch; lia. }
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (Kont _ mdc mj (2^64 - 1)).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
eapply presxD_trans; [exact PRES | exact HPRj].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply jroot_rep_agree; [exact JR0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [eapply presxD_trans; [exact PRES | exact HPRj] | exact HP | incl_tac | incl_tac | clia].
+ right. split; [reflexivity|]. exists A1. split; [exact DC|].
eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
-
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INq2 : In (q, nq) (BS ++ CBS ++ LB)) by (apply in_or_app; right; apply in_or_app; left; exact INq).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp2) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q nq HP INq2) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q nq HP INq2) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi.
assert (NIq : ~ In (q, nq) (BS ++ LB)) by (exact (nodup_mid_notin BS CBS LB q nq nq (heap_blk_nodup S4L HIx _ _ _ _ HP) INq)).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (q + 8, q + 16)] mc) as MU.
stash G. stash CLOSE.
apply rz_evt; [exact MOK|].
bstep. bstep. if_falsex. bstep. bstep. bstep. bstep.
do 10 bstep.
apply evt_RZ_done. unstash G. unstash CLOSE.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) mc mj).
{ eapply presxD_of_munch; [exact MU | exact WM |].
eapply (client_outsideD S4L HIx); [exact HP | incl_tac | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq. split; [exact INq2 | split; [exact NIq | lia]]. }
eapply (Kont _ mdc mj 1).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
eapply presxD_trans; [exact PRES | exact HPRj].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply jroot_rep_agree; [exact JR0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [eapply presxD_trans; [exact PRES | exact HPRj] | exact HP | incl_tac | incl_tac | clia].
+ left. split; [reflexivity|]. exists A1, q, CBS. split; [exact Hq|]. split; [exact DC|]. split.
* apply CLOSE; [exact QH | exact MU | exact WM].
* eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia|]. apply Forall_cons; [| apply Forall_nil].
cbn [fst snd]. right; left. exists q, nq. split; [exact INq2 | lia].
Qed.

#[using="LO LOS SPA RA SPD DHI DAL NN JR0 Kont"] Lemma sh_join :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : Model) (q ty tojs : Z) (dold errc : word),
sh_inv mc mdc -> fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc (p + 8) [C8 (wz tojs)] ->
( (q = 0 /\ exists A', HEAPx A' (BS ++ LB) mc mdc)
\/ (q <> 0 /\ exists A' CBS nq tojs0, HEAPx A' (BS ++ CBS ++ LB) mc mdc /\ In (q, nq) CBS /\ 16 <= nq /\
rw_cells rsegs mc q [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] /\
(forall m', rw_cells rsegs m' q [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ->
munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono rsegs mc m' -> scopy S4L S4F r m' CBS q)) ) ->
realizes rsegs (mkCfg (MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) (wz q) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x26c2c) fc1 None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros (VM & PRES & ST & FR & G) FS FRM DC ERR SRC8 NODE.
unfold sh_frame in FR. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (HD0 : 0 < D < 2^64) by (first [pose proof (rw_cells_bound _ _ _ _ DC) as HB | pose proof (rw_cells_bound _ _ _ DC) as HB]; cbn in HB; lia).
destruct (jroot_rep_root_in S4L S4F r m0 BS p JR0 NN) as (np & INp & Hnp).
destruct NODE as [(-> & A1 & HP) | (Hq & A1 & CBS & nq & tojs0 & HP & INq & Hnq & QH & CLOSE)].
-
pose proof (heap_blk S4L HIx _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (490332, 490336)] mc) as MU.
stash G.
apply rz_evt; [exact MOK|].
bstepz. bstep. if_true. bstep. bstep. bstep. bstep. bstep. bstepz. bstep.
do 10 bstep.
apply evt_RZ_done. unstash G.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) mc mj).
{ eapply presxD_of_munch; [exact MU | exact WM |].
eapply (client_outsideD S4L HIx); [exact HP | incl_tac | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. intros; simpl hl_scratch; lia. }
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
eapply (Kont _ mdc mj (2^64 - 1)).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
eapply presxD_trans; [exact PRES | exact HPRj].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply jroot_rep_agree; [exact JR0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [eapply presxD_trans; [exact PRES | exact HPRj] | exact HP | incl_tac | incl_tac | clia].
+ right. split; [reflexivity|]. exists A1. split; [exact DC|].
eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU). solve_frameW_with HP.
-
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INq2 : In (q, nq) (BS ++ CBS ++ LB)) by (apply in_or_app; right; apply in_or_app; left; exact INq).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp2) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q nq HP INq2) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q nq HP INq2) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi.
assert (NIq : ~ In (q, nq) (BS ++ LB)) by (exact (nodup_mid_notin BS CBS LB q nq nq (heap_blk_nodup S4L HIx _ _ _ _ HP) INq)).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (q + 8, q + 16)] mc) as MU.
stash G. stash CLOSE.
apply rz_evt; [exact MOK|].
bstep. bstep. if_falsex. bstep. bstep. bstep. bstep.
do 10 bstep.
apply evt_RZ_done. unstash G. unstash CLOSE.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : heap_presxD S4L D (BS ++ LB) (bv_unsigned sp) mc mj).
{ eapply presxD_of_munch; [exact MU | exact WM |].
eapply (client_outsideD S4L HIx); [exact HP | incl_tac | clia |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq. split; [exact INq2 | split; [exact NIq | lia]]. }
eapply (Kont _ mdc mj 1).
+ unfold jf_postD. cbn [hl_segs hl_tp hl_volatile S4L].
split; [apply ret_statew_intro; [eapply fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
eapply presxD_trans; [exact PRES | exact HPRj].
+ eapply jc_glob_P_munch; [exact G | exact MU | exact WM |].
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply jroot_rep_agree; [exact JR0 | | apply incl_refl].
eapply (presxD_agree S4L HIx); [eapply presxD_trans; [exact PRES | exact HPRj] | exact HP | incl_tac | incl_tac | clia].
+ left. split; [reflexivity|]. exists A1, q, CBS. split; [exact Hq|]. split; [exact DC|]. split.
* apply CLOSE; [exact QH | exact MU | exact WM].
* eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia|]. apply Forall_cons; [| apply Forall_nil].
cbn [fst snd]. right; left. exists q, nq. split; [exact INq2 | lia].
Qed.

Definition sh_regs (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) a0 (wz 0x13938) a2 a3 (wz D) a5 a6 a7
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma sh_bool :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (bw dold errc : word) (junk : list byte),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_BOOLEAN 1 tojs pb udel ud ++ [C4 bw; CB 4 junk]) ->
(forall m' q (bw' : word) (junk' : list byte),
rw_cells rsegs m' q (jhdr_cells JT_BOOLEAN 1 tojs 0 0 0 ++ [C4 bw'; CB 4 junk']) -> scopy S4L S4F r m' [(q, 48)] q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x269cc) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until junk. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold sh_frame in FR. unfold sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (rw_cells_bound rsegs mc p _ SRC) as PB. cbn [cells_size csize Nat.add jhdr_cells app] in PB.
unfold jhdr_cells in SRC. cbn [app] in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
bstep. if_true.
apply evt_RZ_done. apply (proj1 (rw_cells_app rsegs m2 p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs m2 (p + 8) [_] _)) in SRC8 as [SRC8 _].
eapply sh_join with (ty := JT_BOOLEAN) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
pose proof (munch_refl [(q, q + 48)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2.
reenter MOK2.
bstep. if_falsex.
do 5 bstep. bstepz. bstepz. bstepz. bstepz. bstepz. bstep. bstep.
unstash G2. unstash SCB.
apply evt_RZ_done.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _].
jhdr_split BLK.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP3 : HEAPx A2 ((q, 48) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI end.
extend_presD S4L HIx PRES MU WM HP2.
eapply sh_join with (ty := JT_BOOLEAN) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | ]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | ].
{ eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia. }
right. split; [exact Hq|]. exists A2, [(q, 48)], 48, (fn_bool_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP3 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. eapply (SCB m' q).
unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
Qed.

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma sh_double :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud : Z) (bits dold errc : word),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 48 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_DOUBLE 1 tojs pb udel ud ++ [C8 bits]) ->
(forall m' q, rw_cells rsegs m' q (jhdr_cells JT_DOUBLE 1 tojs 0 0 0 ++ [C8 bits]) -> scopy S4L S4F r m' [(q, 48)] q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x26aec) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until errc. intros INV HP INp Hnp DC ERR SRC SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold sh_frame in FR. unfold sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (rw_cells_bound rsegs mc p _ SRC) as PB. cbn [cells_size csize Nat.add jhdr_cells app] in PB.
unfold jhdr_cells in SRC. cbn [app] in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
bstep. bstep. bstep.

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
extend_presD S4L HIx PRES MU WM HP. extend_presD_call PRES HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]. cbn [hl_segs S4L] in DC.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]. cbn [hl_segs S4L] in SRC.
unstash G. pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2. clear G.
lazymatch goal with |- realizes _ (mkCfg (MS _ ?Fx _ _ _ _ _) _) _ =>
assert (FS8 : fsv8 F Fx) by (apply fsv8_set8; [reflexivity | apply fsv8_refl]) end.
clear MU WM MI ST.
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
reenter MOK2.
bstep. if_true.
apply evt_RZ_done. apply (proj1 (rw_cells_app rsegs m2 p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs m2 (p + 8) [_] _)) in SRC8 as [SRC8 _].
eapply sh_join with (ty := JT_DOUBLE) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| exact FS8 | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ].
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ q 48 HP2 ltac:(left; reflexivity)) as Hqimg. cbn [hl_img_lo hl_img_hi S4L] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1)).
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 48 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp.
pose proof (munch_refl [(q, q + 48)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
stash G2. stash FS8.
reenter MOK2.
bstep. if_falsex.
do 5 bstep. bstepz. bstepz. bstepz. bstepz. bstepz. bstep. bstep.
unstash G2. unstash SCB. unstash FS8.
apply evt_RZ_done.
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X. destruct X as [_ SRC8]. cbn [cells_size csize Nat.add app] in SRC8.
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _].
jhdr_split BLK.
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X. destruct X as [QH QT]. cbn [cells_size csize Nat.add app] in QT.
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
assert (HP3 : HEAPx A2 ((q, 48) :: BS ++ LB) mx md2) by heap_now S4L HIx HP2 MU WM MI end.
extend_presD S4L HIx PRES MU WM HP2.
eapply sh_join with (ty := JT_DOUBLE) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | ]]]]
| exact FS8 | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | ].
{ eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia. }
right. split; [exact Hq|]. exists A2, [(q, 48)], 48, (fn_dbl_to_json_string S4F).
split; [eapply (heap_perm S4L HIx); [exact HP3 | perm] |].
split; [left; reflexivity|]. split; [lia|]. split; [exact QH|].
intros m' QH' MU' WM'. eapply (SCB m' q).
unfold jhdr_cells. cbn [app].
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)). split; [exact QH'|]. cbn [cells_size csize Nat.add app].
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]. cbn. lia.
Qed.

#[using="LO LOS SPA HT RA SPD DHI DAL NN JR0 Kont"] Lemma sh_int :
forall (x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (mdc : Model) (A : AS S4L HIx) (np tojs pb udel ud cty : Z) (v dold errc : word) (junk : list byte),
sh_inv mc mdc -> HEAPx A (BS ++ LB) mc mdc -> In (p, np) BS -> 56 <= np ->
rw_cells rsegs mc D [C8 dold] -> rw_cells rsegs mc (0x77c00 - 164) [C4 errc] ->
rw_cells rsegs mc p (jhdr_cells JT_INT 1 tojs pb udel ud ++ [C4 (wz cty); CB 4 junk; C8 v]) -> (cty = 0 \/ cty = 1) ->
(forall m' q (junk' : list byte),
rw_cells rsegs m' q (jhdr_cells JT_INT 1 tojs 0 0 0 ++ [C4 (wz cty); CB 4 junk'; C8 v]) -> scopy S4L S4F r m' [(q, 56)] q) ->
realizes rsegs (mkCfg (MS (sh_regs x1 t0 t1 t2 a0 a2 a3 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6)
F (wz 0x26a84) fc None mc (seg_rom rsegs)) mdc) T.
Proof.
intros until junk. intros INV HP INp Hnp DC ERR SRC CTY SCB. pose proof INV as (VM & PRES & ST & FR & G).
unfold sh_frame in FR. unfold sh_regs. unfold SH_STK_P in LOS. unfold_consts. word_range sp SPR.
change (0x77c00 - 164) with 490332 in ERR.
assert (INp1 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heap_blk S4L HIx _ _ _ _ p np HP INp1) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ p np HP INp1) as Hpimg. cbn [hl_img_lo hl_img_hi S4L] in Hpimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (rw_cells_bound rsegs mc p _ SRC) as PB. cbn [cells_size csize Nat.add jhdr_cells app] in PB.
unfold jhdr_cells in SRC. cbn [app] in SRC.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] mc) as MU.
stash G. stash SCB.
apply rz_evt; [exact MOK|].
bstep. norm_sx32. bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (TAIL : forall (pc1 ret1 : Z),
(pc1 = 0x26a94 /\ ret1 = 0x26aa0 /\ cty = 0 \/ pc1 = 0x26be4 /\ ret1 = 0x26bf0 /\ cty = 1) ->
evt rsegs (RZ rsegs mdc T)
(MS (mkR x1 (wz (bv_unsigned sp + -64)) gp (wz 0x77c00) t0 t1 t2 (wz p) (wz D) (wz cty) (wz 1) a2 a3 (wz D) a5 a6 a7
x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pc1) fc None mx (seg_rom rsegs))) end.
2:{ destruct CTY as [-> | ->].
- bstep. if_false. bstep. if_false. eapply TAIL. left. repeat split; reflexivity.
- bstep. if_true. eapply TAIL. right. repeat split; reflexivity. }
intros pc1 ret1 ARM.
destruct ARM as [(-> & -> & ->) | (-> & -> & ->)]; (bstep; bstep; bstep;

alloc_call (hi_malloc S4L HIx) S4L HIx HP MU WM MI;
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 OUT2; open_ret RS; cbn [hl_segs S4L] in *;
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia; rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia;
extend_presD S4L HIx PRES MU WM HP; extend_presD_call PRES HPR2;
(apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]); cbn [hl_segs S4L] in FR;
(apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in DC; [| left; cbn; lia]); cbn [hl_segs S4L] in DC;
(apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in SRC; [| eapply client_range_block; [exact INp1 | lia | cbn; lia]]); cbn [hl_segs S4L] in SRC;
unstash G; pose proof (jc_glob_P_pres _ _ _ _ HPR2 (jc_glob_P_munch _ _ _ G MU WM ltac:(repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia))) as G2; clear G;
clear MU WM MI ST;
destruct OUT2 as [(-> & _ & HP2) | (Hq & [junk0 BLK] & HP2)];
[
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2;
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI; cbn [hl_segs S4L] in MI;
pose proof (munch_refl [] m2) as MU; pose proof (wmono_refl rsegs m2) as WM;
reenter MOK2;
bstep; if_true;
apply evt_RZ_done; apply (proj1 (rw_cells_app rsegs m2 p [_; _] _)) in SRC as X; destruct X as [_ SRC8]; cbn [cells_size csize Nat.add app] in SRC8;
apply (proj1 (rw_cells_app rsegs m2 (p + 8) [_] _)) in SRC8 as [SRC8 _];
eapply sh_join with (ty := JT_INT) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | exact G2]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | left; split; [reflexivity | exists A2; exact HP2] ]
|
change (Z.to_nat 56) with 56%nat in BLK;
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2;
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI; cbn [hl_segs S4L] in MI;
pose proof (heap_blk S4L HIx _ _ _ _ q 56 HP2 ltac:(left; reflexivity)) as (_ & Hqal & Hqlo & Hqhi & _);
pose proof (heap_blk_img S4L HIx _ _ _ _ q 56 HP2 ltac:(left; reflexivity)) as Hqimg; cbn [hl_img_lo hl_img_hi S4L] in Hqimg;
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi;
assert (Hqp : q <> p) by (intros ->; exact (fresh_not_in S4L HIx _ _ _ _ _ _ np HP2 INp1));
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ q 56 p np HP2 ltac:(left; reflexivity) ltac:(right; exact INp1) Hqp) as Hdqp;
pose proof (munch_refl [(q, q + 56)] m2) as MU; pose proof (wmono_refl rsegs m2) as WM;
stash G2;
reenter MOK2;
bstep; if_falsex;
do 5 bstep; bstepz; bstepz; bstepz; bstepz; bstepz; bstepz; step_until 0x26c2c;
unstash G2; unstash SCB;
apply evt_RZ_done;
apply (proj1 (rw_cells_app rsegs _ p [_; _] _)) in SRC as X; destruct X as [_ SRC8]; cbn [cells_size csize Nat.add app] in SRC8;
apply (proj1 (rw_cells_app rsegs _ (p + 8) [_] _)) in SRC8 as [SRC8 _];
jhdr_split BLK;
apply (proj1 (rw_cells_app rsegs _ q [_; _; _] _)) in BLK as X; destruct X as [QH QT]; cbn [cells_size csize Nat.add app] in QT;
lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ =>
assert (HP3 : HEAPx A2 ((q, 56) :: BS ++ LB) my md2) by heap_now S4L HIx HP2 MU WM MI end;
extend_presD S4L HIx PRES MU WM HP2;
eapply sh_join with (ty := JT_INT) (tojs := tojs);
[ split; [eapply model_vm_only_trans; [exact VM | exact VM2] | split; [exact PRES | split; [exact ST2 | split; [exact FR | ]]]]
| apply fsv8_refl | intros Hf; exact Hf | exact DC | exact ERR2 | exact SRC8 | ];
[ eapply jc_glob_P_outside; [exact G2 | exact MU | exact WM |]; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia |];
right; split; [exact Hq|]; exists A2, [(q, 56)], 56, (fn_int_to_json_string S4F);
split; [eapply (heap_perm S4L HIx); [exact HP3 | perm] |];
split; [left; reflexivity|]; split; [lia|]; split; [exact QH|];
intros m' QH' MU' WM'; eapply (SCB m' q);
unfold jhdr_cells; cbn [app];
apply (proj2 (rw_cells_app rsegs m' q [_; _; _] _)); split; [exact QH'|]; cbn [cells_size csize Nat.add app];
eapply (rw_cells_transport rsegs); [exact QT | exact MU' | exact WM' |]; cbn; lia ]).
Qed.
End ShallowP.

End RC__3.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uxk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uxk8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PutX.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo : Z) (errv : word) (BS : list blk) (x : Z) (T : TSet).

#[using="Type"] Lemma mf_xstr :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte),
HEAPx A (BS ++ LB) m md ->
xstr S4L S4F m BS x 0 ->
mf_frame ra sp s0 s1 m junk8 ->
stk rsegs m lo (bv_unsigned sp + -32) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB lo errv Sbool BS x 1 T ->
realizes rsegs (mkCfg (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x248c8) fc1 None m (seg_rom rsegs)) md) T.
Proof.
intros until junk8. intros HP J FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM K.
unfold mf_frame in FR. unfold_consts. word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(x, x + 40)] m) as MU.
destruct J as (pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS BS.
-
cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
unfold jhdr_cells in HDR. cbn [app] in HDR. cbn [hl_segs S4L] in HDR.
apply rz_evt; [exact MOK|].
bstep. norm_w32. bstep. bstepz. bstepz. bstep. if_truex.
bstep. bstep. if_truex.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; apply in_or_app; right; exact Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).
apply evt_RZ_done.
eapply mf_gen; [exact HP2 | unfold jhdr_cells; cbn [app]; exact HDR | | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | exact VM0 | eapply heap_pres_trans; [exact HPR | exact HPR2] | exact FS | exact FRM | reflexivity | exact K].
eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG2 | intros b Hb; apply in_or_app; left; exact Hb] | apply incl_refl].
-
cbn [app] in HP.
pose proof (heap_blk S4L HIx _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x (48 + cap) HP ltac:(left; reflexivity)) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
pose proof (heap_blk S4L HIx _ _ _ _ pd pdn HP ltac:(right; left; reflexivity)) as (Hpdn & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi, Hphi.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hxpd.
clear HD.
unfold jhdr_cells in HDR. cbn [app] in HDR. cbn [hl_segs S4L] in HDR.
apply rz_evt; [exact MOK|].
bstep. norm_w32. bstep. bstepz. bstepz. bstep. if_truex.
bstep. bstep. if_falsex. bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
destruct (blk_write S4L HIx _ _ _ _ _ _ _ _ LB (bv_unsigned sp) HP MU WM MI
ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil]) ltac:(intros b Hb; right; apply in_or_app; right; exact Hb) ltac:(clia))
as (HP2 & AG2 & HPR2).

alloc_call (hi_free S4L HIx) S4L HIx HP MU WM MI.
{ right. exists pdn. right; left. reflexivity. }
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in HPR3 by lia.
rewrite lb_remove_other in HPR3, HP3 by (cbn; lia). rewrite lb_remove_head in HPR3, HP3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in HDR.
assert (OPB3 : opt_pbuf rsegs m3 PBS pb).
{ eapply opt_pbuf_agree; [exact OPB | | apply incl_refl]. eapply agree_on_trans.
- eapply agree_on_incl; [exact AG2 | intros b Hb; right; apply in_or_app; left; exact Hb].
- eapply (agree_of_heap_pres rsegs S4L); [exact HPR3 | reflexivity | intros b Hb; right; apply in_or_app; left; exact Hb]. }
assert (HPRb : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPR2|].
eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; right; apply in_or_app; right; exact Hb]. }
replace (ret_pc (Z_to_bv 64 0x2491c)) with (Z_to_bv 64 0x2491c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
eapply mf_gen; [exact HP3 | unfold jhdr_cells; cbn [app]; exact HDR | exact OPB3 | exact FR | exact ST3 | clia | clia | exact SPA | exact HT
| exact ERR3 | exact RA | eapply model_vm_only_trans; [exact VM0 | exact VM3] | exact HPRb | exact FS | exact FRM | reflexivity | exact K].
Qed.

End PutX.
End RC__1.

Ltac mfx_prologue HIx BS LB x sp mm HP HDR ST INx INx2 n :=
let MOK := fresh "MOK" in let MI := fresh "MI" in let WM := fresh "WM" in let MU := fresh "MU" in
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK;
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI;
pose proof (wmono_refl rsegs mm) as WM;
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (x + 4, x + 8)] mm) as MU;
unfold jhdr_cells in HDR; cbn [app] in HDR; cbn [hl_segs S4L] in HDR;
apply rz_evt; [exact MOK|];
carve_frame 32%nat ST;
bstep; bstep; bstep; bstep; bstep; bstep; norm_w32; bstep; norm_w32; bstepz;
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
lazymatch type of HP with HEAP _ _ ?AA _ _ ?mdd =>
assert (AG1 : agree_on rsegs (others x (BS ++ LB)) mm mx);
[ eapply (agree_others_gen rsegs); [exact MU | exact WM |];
intros a' k' Hin' Hne';
pose proof (heap_blk S4L HIx _ _ _ _ a' k' HP Hin') as (Hk' & _ & _ & Hahi' & _);
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ x n a' k' HP INx2 Hin' ltac:(congruence)) as D';
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'; cbn; lia
| assert (HP1 : HEAP S4L HIx AA (BS ++ LB) mx mdd);
[ eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP MU);
apply Forall_cons; [cbn [fst snd]; left; split; [clia | pose proof (hi_top_hi S4L HIx); lia] |];
apply Forall_cons; [cbn [fst snd]; right; left; exists x, n; split; [exact INx2 | lia] | apply Forall_nil]
| assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) mm mx);
[ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outside S4L HIx); [exact HP | intros b' Hb'; apply in_or_app; right; exact Hb' | clia |];
apply Forall_cons; [cbn [fst snd]; left; clia |];
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]; right; left; exists x, n; split; [exact INx2|]; split; [| lia];
exact (nodup_prefix_suffix BS LB x n n (heap_blk_nodup S4L HIx _ _ _ _ HP) INx)
| bstep; if_true; replace (1 + -1) with 0 in HDR by lia; bstep; bstep; if_true; clear MU WM MI; rename mx into m1 ] ] ]
end end.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require Import TopUbTac.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma maybe_free_x_cps (HIx : heap_iface S4L) :
forall (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word) (BS : list blk) (x : Z) (r : jroot),
HEAP S4L HIx A (BS ++ LB) m md ->
jroot_rep S4L S4F r m BS x -> match r with JRdblx _ | JRstrx => True | _ => False end ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 32 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 x -> a1 = Z_to_bv 64 0 ->
KPOST HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo errv Sbool BS x 1 T ->
realizes rsegs (mkCfg (MS (mkR ra sp gp (Z_to_bv 64 0x77c00) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x24874) fc None m (seg_rom rsegs)) md) T.
Proof.
intros until r. intros HP J XL ST LO LOS SPA HT ERR RA A0 A1 K.
unfold_consts. word_range sp SPR. subst a0 a1.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
destruct r as [|s|tojs|]; try contradiction.
-
destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR).
assert (INx : In (x, 48) BS) by (rewrite EBS; left; reflexivity).
assert (INx2 : In (x, 48) (BS ++ LB)) by (apply in_or_app; left; exact INx).
pose proof (heap_blk S4L HIx _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x 48 HP INx2) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
mfx_prologue HIx BS LB x sp m HP HDR ST INx INx2 48.
assert (AGT : agree_on rsegs PBS m m1).
{ eapply agree_on_incl; [exact AG1|]. rewrite EBS. cbn [app].
apply (incl_others_tail x 48 PBS LB PBS); [rewrite EBS in ND; exact ND | intros b Hb; apply in_or_app; left; exact Hb]. }
rewrite EBS in HP1. cbn [app] in HP1.
apply evt_RZ_done. eapply (mf_scalar HIx) with (n := 48) (rest := [C8 bits]) (u1 := 0) (u2 := 0);
[exact HP1 | unfold jhdr_cells; cbn [app]; exact HDR | reflexivity | right; left; reflexivity
| eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]
| exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | reflexivity | exact K].
-
pose proof J as J0. destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES).
assert (INx : In (x, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
assert (INx2 : In (x, 48 + cap) (BS ++ LB)) by (apply in_or_app; left; exact INx).
pose proof (heap_blk S4L HIx _ _ _ _ x (48 + cap) HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ x (48 + cap) HP INx2) as Hximg. cbn [hl_img_lo hl_img_hi S4L] in Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
destruct CASES as [(Hl0 & EDBS & Hfit & junk & HDR) | (Hl0 & pd & pdn & junk & junk2 & EDBS & HPD & HDR & HD)]; subst DBS.
+ mfx_prologue HIx BS LB x sp m HP HDR ST INx INx2 (48 + cap).
assert (AGT : agree_on rsegs PBS m m1).
{ eapply agree_on_incl; [exact AG1|]. rewrite EBS. cbn [app].
apply (incl_others_tail x (48 + cap) PBS LB PBS); [rewrite EBS in ND; exact ND | intros b Hb; apply in_or_app; left; exact Hb]. }
apply evt_RZ_done. eapply (mf_xstr HIx);
[exact HP1 | | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | exact K].
exists pb, PBS, [], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | exact AGT | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. left.
split; [exact Hl0|]. split; [reflexivity|]. split; [exact Hfit|]. exists junk. unfold jhdr_cells. cbn [app]. exact HDR.
+ mfx_prologue HIx BS LB x sp m HP HDR ST INx INx2 (48 + cap).
assert (AGT : agree_on rsegs ([(pd, pdn)] ++ PBS) m m1).
{ eapply agree_on_incl; [exact AG1|]. rewrite EBS. cbn [app].
apply (incl_others_tail x (48 + cap) ((pd, pdn) :: PBS) LB ((pd, pdn) :: PBS)); [rewrite EBS in ND; exact ND | intros b Hb; apply in_or_app; left; exact Hb]. }
apply evt_RZ_done. eapply (mf_xstr HIx);
[exact HP1 | | exact FR | exact ST | clia | clia | exact SPA | exact HT
| exact ERR | exact RA | apply model_vm_only_refl | exact HPR1 | apply fsaved_refl | intros Hf; exact Hf | exact K].
exists pb, PBS, [(pd, pdn)], cap, len, str. split; [exact EBS|].
split; [eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AGT | intros b Hb; right; exact Hb] | apply incl_refl]|].
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|]. right.
split; [exact Hl0|]. exists pd, pdn, junk, junk2. split; [reflexivity|]. split; [exact HPD|].
split; [unfold jhdr_cells; cbn [app]; exact HDR|].
pose proof (heap_blk S4L HIx _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; rewrite EBS; right; left; reflexivity)) as (Hpdn & _).
eapply rw_cells_agree; [exact HD | exact AGT | exists pd, pdn; split; [left; reflexivity | cbn; lia]].
Qed.

#[using="Type"] Theorem put_xleaf_P : forall HIx : heap_iface S4L, jo_put_xleaf_stmt S4L HIx S4F put_entry_P put_stk_P.
Proof.
intros HIx. unfold jo_put_xleaf_stmt. intros until errv. intros PRE J XL A0 K.
destruct PRE as (HP & ST & LO & LOS & SPA & HT & ERR & TP & RA).
cbn [hl_segs hl_tp S4L] in *. unfold put_stk_P in LOS. unfold put_entry_P.
unfold_consts. word_range sp SPW.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.

assert (Hp : p <> 0) by (destruct r; try contradiction; exact (proj1 J)).
assert (BLK : forall a k, In (a, k) (BS ++ LB) -> 0 <= k /\ a + k <= alloc_ceiling).
{ intros a k Hin. pose proof (heap_blk S4L HIx _ _ _ _ a k HP Hin) as (Hk & _ & _ & Hhi & _). split; [exact Hk | exact Hhi]. }
assert (Rp : 0 < p < 2^64).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (_ & _ & pb & PBS & bits & EBS & _). pose proof (heap_blk S4L HIx _ _ _ _ p 48 HP ltac:(apply in_or_app; left; rewrite EBS; left; reflexivity)) as (_ & _ & Hlo & Hhi & _). clia.
- destruct J as (_ & pb & PBS & DBS & cap & len & str & EBS & _ & Hcap & _). pose proof (heap_blk S4L HIx _ _ _ _ p (48 + cap) HP ltac:(apply in_or_app; left; rewrite EBS; left; reflexivity)) as (_ & _ & Hlo & Hhi & _). clia. }
apply rz_evt; [exact MOK|]. subst a0 tp.
carve_frame 96%nat ST.
do 12 bstep. bstep. if_falsex. bstep. bstep. bstep.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
assert (AG : agree_on rsegs (BS ++ LB) m m1).
{ eapply agree_of_munch; [exact MU | exact WM |]. intros a k Hin. destruct (BLK a k Hin) as [Hk Hhi]. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi. cbn. lia. }
assert (J1 : jroot_rep S4L S4F r m1 BS p).
{ destruct r as [|s|tojs|]; try contradiction.
- destruct J as (Hx & Htojs & pb & PBS & bits & EBS & OPB & HDR). split; [exact Hx|]. split; [exact Htojs|].
exists pb, PBS, bits. split; [exact EBS|]. split.
+ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; left; rewrite EBS; right; exact Hb] | apply incl_refl].
+ eapply rw_cells_agree; [exact HDR | exact AG | exists p, 48; split; [apply in_or_app; left; rewrite EBS; left; reflexivity | cbn; lia]].
- destruct J as (Hx & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & CASES). split; [exact Hx|].
exists pb, PBS, DBS, cap, len, str. split; [exact EBS|]. split.
{ eapply opt_pbuf_agree; [exact OPB | eapply agree_on_incl; [exact AG | intros b Hb; apply in_or_app; left; rewrite EBS; right; apply in_or_app; right; exact Hb] | apply incl_refl]. }
split; [exact Hcap|]. split; [exact Hlen|]. split; [exact Hsl|].
destruct CASES as [(Hl0 & EDBS & Hfit & junkx & HDR) | (Hl0 & pd & pdn & junkx & junkx2 & EDBS & HPD & HDR & HD)].
+ left. split; [exact Hl0|]. split; [exact EDBS|]. split; [exact Hfit|]. exists junkx.
eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [apply in_or_app; left; rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add length app]; rewrite ?length_app; cbn [length]; lia]].
+ right. split; [exact Hl0|]. exists pd, pdn, junkx, junkx2. split; [exact EDBS|]. split; [exact HPD|].
pose proof (heap_blk S4L HIx _ _ _ _ pd pdn HP ltac:(apply in_or_app; left; rewrite EBS, EDBS; right; left; reflexivity)) as (Hpdn & _).
split.
* eapply rw_cells_agree; [exact HDR | exact AG | exists p, (48 + cap); split; [apply in_or_app; left; rewrite EBS; left; reflexivity | rewrite cells_size_app; cbn [cells_size csize jhdr_cells Nat.add]; lia]].
* eapply rw_cells_agree; [exact HD | exact AG | exists pd, pdn; split; [apply in_or_app; left; rewrite EBS, EDBS; right; left; reflexivity | cbn; lia]]. }
assert (HPR1 : heap_pres S4L LB (bv_unsigned sp) m m1).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; apply in_or_app; right; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia | apply Forall_nil]. }
apply evt_RZ_done.
eapply (maybe_free_x_cps HIx) with (BS := BS) (LB := LB) (x := p) (lo := lo) (r := r);
[ heap_now S4L HIx HP MU WM MI | exact J1 | exact XL | .. ]; try alloc_side.
intros ms2 md2 (m2 & A2 & rr & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT2).
destruct RS2 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L] in *.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in HPR2 by lia.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
clear MU WM MI.
destruct OUT2 as [(-> & Hrc2 & _ & _) | [(-> & _ & HP2) | (-> & _ & ZM & _)]]; [lia | | exfalso; cbn in ZM; exact ZM].
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2. pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (wmono_refl rsegs m2) as WM. pose proof (munch_refl [] m2) as MU.
reenter MOK2. bstep. bstep. if_truex.
do 12 bstep. release_frame FR ST2 (bv_unsigned sp). bstep.
apply evt_RZ_done. eapply K.
- unfold jf_post. split; [apply ret_statew_intro; [exact FS2 | exact FRM2] |]. split; [exact VM2|]. split; [exact ST2|].
split; [eapply heap_pres_trans; [exact HPR1 | eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; exact Hb]]|]. exists errv. exact ERR2.
- reflexivity.
- exact ERR2.
- exists A2. exact HP2.
Qed.

End RC__2.
