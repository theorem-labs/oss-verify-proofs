(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27 Q13u QHig QwAs QDM6 QUcd QJFf QBrp Q6sh QKTr QJBH QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk QpY2 QmP7 QUnM QlES.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 QDM6 QUcd QJFf QBrp.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QmP7.Mq0.
Import QUnM.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma zbytes_bound : forall m A n, zbytes m A n -> 0 <= A /\ A + n <= 2^64.
Proof. intros m A n [[H1 [H2 _]] _]. lia. Qed.

Lemma zbytes_store_ok : forall m A n i (j : nat),
zbytes m A n -> 0 <= i -> i + Z.of_nat j <= n -> store_ok asegs m (wa (A + i)) j = true.
Proof. intros m A n i j [W _] Hi Hj. eapply wr_at_store_ok; eauto. Qed.

Lemma zbytes_store_ok_at : forall m A n a (j : nat),
zbytes m A n -> A <= a -> a + Z.of_nat j <= A + n -> store_ok asegs m (wa a) j = true.
Proof. intros m A n a j ZB H1 H2. replace a with (A + (a - A)) by lia. eapply zbytes_store_ok; [exact ZB| lia| lia]. Qed.

Lemma zbytes_write : forall m A n i bs,
zbytes m A n -> 0 <= i -> i + Z.of_nat (length bs) <= n -> Forall (fun b => b = b8 0) bs ->
zbytes (write_to_mem m (wa (A + i)) bs) A n.
Proof.
intros m A n i bs Z0 Hi Hn Hbs. pose proof (zbytes_bound _ _ _ Z0) as [B1 B2]. destruct Z0 as [W Z0]. split.
- apply wr_at_write. exact W.
- intros k Hk.
destruct (Z.lt_ge_cases k i) as [L|GE]; [| destruct (Z.lt_ge_cases k (i + Z.of_nat (length bs))) as [IN|R]].
+ apply bytes_at_write_other; [apply Z0; lia| lia| lia| cbn [length Z.of_nat]; lia].
+ pose proof (bytes_at_write_same asegs m (A + i) bs ltac:(lia) ltac:(lia)) as BW.
assert (E : exists k', (k' < length bs)%nat /\ k = i + Z.of_nat k') by (exists (Z.to_nat (k - i)); split; lia).
destruct E as (k' & Hk' & ->).
destruct BW as (_ & _ & BW). specialize (BW k' Hk').
pose proof (proj1 (List.Forall_forall _ _) Hbs) as FB.
destruct (nth_error bs k') as [b|] eqn:En; [| apply nth_error_None in En; lia].
assert (b = b8 0) as -> by (apply FB; eapply nth_error_In; exact En).
split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i0 Hi0. cbn [length] in Hi0. assert (i0 = 0%nat) as -> by lia.
cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. replace (A + (i + Z.of_nat k')) with (A + i + Z.of_nat k') by lia. exact BW.
+ apply bytes_at_write_other; [apply Z0; lia| lia| lia| cbn [length Z.of_nat]; lia].
Qed.

Lemma zbytes_write_at : forall m A n a bs,
zbytes m A n -> A <= a -> a + Z.of_nat (length bs) <= A + n -> Forall (fun b => b = b8 0) bs ->
zbytes (write_to_mem m (wa a) bs) A n.
Proof.
intros m A n a bs ZB H1 H2 HF. replace a with (A + (a - A)) by lia. apply zbytes_write; [exact ZB| lia| lia| exact HF].
Qed.

Lemma zbytes_write_other : forall m A n a bs,
zbytes m A n -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> (A + n <= a \/ a + Z.of_nat (length bs) <= A) ->
zbytes (write_to_mem m (wa a) bs) A n.
Proof.
intros m A n a bs [W Z0] H1 H2 HD. split; [apply wr_at_write; exact W|].
intros i Hi. apply bytes_at_write_other; [apply Z0; exact Hi| lia| lia| cbn [length Z.of_nat]; lia].
Qed.

Lemma zbytes_transport : forall W m m' A n,
zbytes m A n -> munch W m m' -> wmono asegs m m' -> disjoint_from W A n -> zbytes m' A n.
Proof.
intros W m m' A n [WR Z0] MU WM HD. split; [eapply wr_at_transport; eauto|].
intros i Hi. eapply bytes_at_transport; [apply Z0; exact Hi| exact MU|].
cbn [length Z.of_nat]. revert HD. clear -Hi. induction W as [|[lo hi] W IH]; cbn; [tauto|]. intros [H1 H2]. split; [lia| apply IH; exact H2].
Qed.

Lemma le8_zero : le8 (wz 0) = repeat (b8 0) 8.
Proof. reflexivity. Qed.

Lemma zbytes_read8 : forall m A n i, zbytes m A n -> 0 <= i -> i + 8 <= n ->
bytes_at asegs m (A + i) (le8 (wz 0)).
Proof.
intros m A n i ZB Hi Hn. pose proof (zbytes_bound _ _ _ ZB) as [B1 B2]. destruct ZB as [_ Z0]. rewrite le8_zero.
assert (GEN : forall k j, 0 <= j -> j + Z.of_nat k <= n -> bytes_at asegs m (A + j) (repeat (b8 0) k)).
{ induction k as [|k IH]; intros j Hj Hk.
- split; [lia|]. split; [cbn; lia|]. intros i0 Hi0; cbn in Hi0; lia.
- cbn [repeat]. change (b8 0 :: repeat (b8 0) k) with ([b8 0] ++ repeat (b8 0) k). apply (proj2 (bytes_at_app _ _ _ _ _)).
split; [apply Z0; lia|]. replace (A + j + Z.of_nat (length [b8 0])) with (A + (j + 1)) by (cbn; lia). apply IH; lia. }
apply GEN; [lia| cbn; lia].
Qed.

Lemma zbytes_load8 : forall m A n a, zbytes m A n -> A <= a -> a + 8 <= A + n ->
ov_read_bytes asegs m (wa a) 8 = Some (le8 (wz 0)).
Proof.
intros m A n a ZB H1 H2.
pose proof (zbytes_read8 m A n (a - A) ZB ltac:(lia) ltac:(lia)) as B. replace (A + (a - A)) with a in B by lia.
pose proof (bytes_at_ov_read asegs m a (le8 (wz 0)) 0%nat 8%nat B ltac:(rewrite length_le8; lia)) as R.
rewrite Z.add_0_r in R. exact R.
Qed.

Lemma zbytes_cells_C8x2 : forall m A n a, zbytes m A n -> A <= a -> a + 16 <= A + n ->
rw_cells asegs m a [C8 (wz 0); C8 (wz 0)].
Proof.
intros m A n a ZB H1 H2. pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_read8 m A n (a - A) ZB ltac:(lia) ltac:(lia)) as R1.
pose proof (zbytes_read8 m A n (a + 8 - A) ZB ltac:(lia) ltac:(lia)) as R2.
replace (A + (a - A)) with a in R1 by lia. replace (A + (a + 8 - A)) with (a + 8) in R2 by lia.
destruct ZB as [[_ [_ W]] _].
split; [split; [cbn; auto|]|].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact R1|]. rewrite length_le8. exact R2.
- split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace (a + i) with (A + (a - A + i)) by lia. apply W. lia.
Qed.

Lemma Forall_zero_1 : Forall (fun b => b = b8 0) [b8 0].
Proof. repeat constructor. Qed.
Lemma Forall_zero_le8 : Forall (fun b => b = b8 0) (le8 (wz 0)).
Proof. rewrite le8_zero. repeat constructor. Qed.
Lemma Forall_zero_le4 : Forall (fun b => b = b8 0) (le4 (wz 0)).
Proof. change (le4 (wz 0)) with (repeat (b8 0) 4). repeat constructor. Qed.
Ltac is_zero_bytes bs :=
lazymatch bs with
| [Z_to_bv 8 0] => idtac
| le8 (Z_to_bv 64 0) => idtac
| le4 (Z_to_bv 64 0) => idtac
| le1 (Z_to_bv 64 0) => idtac
end.
Ltac zero_bytes_forall :=
first [ exact Forall_zero_1 | exact Forall_zero_le8 | exact Forall_zero_le4
| change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; exact Forall_zero_1 ].

Ltac transport_chunks_zb segs m a bs :=
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_write_other m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| is_zero_bytes bs; apply (zbytes_write_at m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | zero_bytes_forall ]
| idtac "note: dropping zbytes hypothesis (store inside, not zeros):" H; clear H ]
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end.

Ltac transport_zb_only m a bs :=
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_write_other m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| is_zero_bytes bs; apply (zbytes_write_at m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | zero_bytes_forall ]
| idtac "note: dropping zbytes hypothesis (store inside, not zeros):" H; clear H ]
end.

Ltac zb_transport m m' MUc WMc :=
let W := lazymatch type of MUc with munch ?W _ _ => W end in
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_transport W m m' A2 n2) in H; [ | exact MUc | exact WMc | cbn [disjoint_from]; slia ]
| idtac "note: dropping zbytes hypothesis (not disjoint from callee footprint):" H; clear H ]
end.

Ltac post_call_zb segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
zb_transport m m' MUc WMc;
repeat match goal with
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_chain' _ m m' W m0 MUc) in H; [| sub_fp_solve]
| fail 100 "callee footprint interval not inside the caller footprint (sub_fp_solve)" ]
end;
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).

Ltac call_zb SPEC tac :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
eapply evt_cut;
[ eapply SPEC
| let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; hnf in PO; tac PO; revert ms' PO; post_call_zb segs m ]
end.

Ltac call_sp_zb SPEC tac :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call_zb SPEC tac; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call_zb SPEC tac; unname_sp
| _ => call_zb SPEC tac
end.

Ltac zstore ZB SOK :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?bs) _) =>
change (write_to_mem m (Z_to_bv 64 a) bs) with (write_to_mem m (wa a) bs);
lazymatch goal with
| MI : mem_inv _ m |- _ => apply (mem_inv_store asegs m (wa a) bs) in MI; [| exact SOK]
end;
clear SOK;
transport_chunks_zb asegs m a bs;
footprint_after_store asegs m a bs;
let m' := fresh "m" in set (m' := write_to_mem m (wa a) bs) in *; clearbody m'; try clear m
end.

Ltac bytes_eq_tac :=
cbn [cells_bytes cbytes app]; rewrite ?le8_lit, ?le4_lit, ?le2_lit, ?le1_lit; cbn [Z_to_le_bytes Z.shiftr Z.shiftl Pos.iter Z.div2];
repeat (first [reflexivity | apply (f_equal2 cons); [apply b8_eqm; vm_compute; reflexivity|]]).

Ltac recast H cs' :=
apply (rw_cells_recast' asegs _ _ _ cs') in H; [| cbn; repeat split; reflexivity | bytes_eq_tac].

Ltac has_var e := match e with context [bv_unsigned _] => idtac end.
Ltac fold_swrap :=
repeat match goal with
| |- context [bv_swrap 32 ?e] =>
first [ has_var e; fail 1
| let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v ]
end.

Ltac at_spin :=
lazymatch goal with |- at_nodeA _ _ NSetTid (MS _ _ (Z_to_bv 64 ?pc) _ None _ _) =>
cbn [at_nodeA]; split; [reflexivity|];
unfold RiscvSemantics.step_accesses; cbn [ms_pc ms_pc_val MS];
match goal with |- context [fetch_word ?s ?p] =>
let w := eval vm_compute in (fetch_word s p) in replace (fetch_word s p) with w by (vm_compute; reflexivity) end;
unfold decode_exec_accesses;
match goal with |- context [is_ecall ?w] =>
let b := eval vm_compute in (is_ecall w) in replace (is_ecall w) with b by (vm_compute; reflexivity) end;
match goal with |- context [decode_any ?w] =>
let d := eval vm_compute in (decode_any w) in replace (decode_any w) with d by (vm_compute; reflexivity) end;
cbn; unfold rset, with_pc; cbn;
replace (Z_to_bv 64 pc + sext 64 0)%bv with (Z_to_bv 64 pc) by (apply bv_eq; vm_compute; reflexivity);
reflexivity
end.

Lemma u64arr_snoc_junk : forall m A ws, u64arr asegs m A ws ->
hjunk m (A + 8 * Z.of_nat (length ws)) (A + 8 * Z.of_nat (length ws) + 8) ->
exists w, u64arr asegs m A (ws ++ [w]).
Proof.
intros m A ws [B W] HJ. destruct (hjunk_C8 m _ HJ) as [w [[_ Bw] Ww]].
cbn [cells_bytes cbytes app cells_size csize Nat.add] in Bw, Ww. rewrite app_nil_r in Bw.
exists w. split.
- rewrite u64s_app. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B|]. rewrite u64s_length. cbn [u64s]. rewrite app_nil_r.
replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact Bw.
- destruct W as (W1 & W2 & W). destruct Ww as (V1 & V2 & V). rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases i (8 * Z.of_nat (length ws))); [apply W; lia|].
replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply V. lia.
Qed.

Lemma slot24_geom {BAND : Band} : forall a G RE X m j t, RPrim a G RE X m -> rlay_ok RE X -> tag_at G 24 j = Some t ->
let B := slot_beg RE 24 j in
0 <= j /\ B = reg_beg (ae_L RE) 24 + j * 8192
/\ reg_beg (ae_L RE) 24 <= B /\ B + 8192 <= reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)
/\ c_alloc_user (cls a 24) <= c_mapped_user (cls a 24) /\ c_mapped_user (cls a 24) <= kFreeArrayOffset
/\ reg_beg (ae_L RE) 24 = prim_lo RE + 24 * 4294967296
/\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo /\ prim_hi RE = prim_lo RE + 137438957568
/\ B mod 16 = 0 /\ prim_lo RE mod 65536 = 0.
Proof.
intros a G RE X m j t RP RL Ht.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as CR.
pose proof (crep_slot_geom a G RE X m 24 (K 24) j t CR ltac:(lia) Ht) as (I0 & I1 & _ & _ & SB & AU & MU & _).
rewrite class_size_24 in *.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & _ & PAL & PK & PH & PHE & _).
cbv zeta. rewrite ?KHI_eq. repeat split; try lia.
all: rewrite SB, RB; Z.div_mod_to_equations; lia.
Qed.

Lemma alloc_user_bounds : forall a G RE X m c, RPrim a G RE X m -> 0 <= c < 32 ->
0 <= c_alloc_user (cls a c) /\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset.
Proof.
intros a G RE X m c RP Hc. destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & _).
destruct (HCall c ltac:(rewrite K32; lia)) as (_ & PU & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5). lia.
Qed.

Lemma hjunk_C8x4 : forall m a, hjunk m a (a + 32) -> exists w0 w1 w2 w3 : word, rw_cells asegs m a [C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
intros m a HJ. destruct (hjunk_split m a (a + 16) (a + 32) HJ ltac:(lia)) as [H1 H2].
destruct (hjunk_C8x2 m a H1) as (w0 & w1 & C1). replace (a + 32) with (a + 16 + 16) in H2 by lia.
destruct (hjunk_C8x2 m (a + 16) H2) as (w2 & w3 & C2).
exists w0, w1, w2, w3. apply (proj2 (rw_cells_app asegs m a [C8 w0; C8 w1] [C8 w2; C8 w3])). split; [exact C1|]. cbn. exact C2.
Qed.

Lemma rw_cells_C8_u64arr1 : forall m A (w : word), rw_cells asegs m A [C8 w] -> u64arr asegs m A [w].
Proof.
intros m A w [[_ B] W]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
split; [cbn [u64s]; rewrite app_nil_r; exact B| cbn [length Z.of_nat]; exact W].
Qed.

Lemma fp_RPrim_not_Tq {BAND : Band} : forall G RE X x, rlay_ok RE X -> fp_RPrim G RE X x -> ~ (rl_T X + 80 <= x < rl_T X + 208).
Proof.
intros G RE X x RL F. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & K32 & _).
rewrite ?KHI_eq in *. unfold prim_lo, prim_hi, region_info in *.
destruct F as [F|[F|[F|[F|[[F _]|[F _]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. unfold region_info in *. lia.
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. lia.
- destruct F as (c & Hc & F1 & F2). unfold fa_beg, reg_beg in *. rewrite KR, KO, KS, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold fa_beg, reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, KS, K32 in *.
Z.div_mod_to_equations. nia.
- destruct F as (c & Hc & F1 & F2). unfold reg_beg in *. rewrite KR, KO, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, K32 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma fp_RPrim_not_slot {BAND : Band} : forall a G RE X m c i t x,
RPrim a G RE X m -> rlay_ok RE X -> tag_at G c i = Some t -> tag_prim t = false ->
fp_RPrim G RE X x -> ~ in_iv (slot_beg RE c i, class_size c) x /\ ~ in_sh (slot_beg RE c i, class_size c) x.
Proof.
intros a G RE X m c i t x RP RL Ht Hp F.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (tag_at_Some_lt G c i t Ht) as [I0 I1].
assert (NE : G c <> []) by (intros E; unfold ncarved in I1; rewrite E in I1; cbn in I1; lia).
pose proof (GNE c NE) as Hc. rewrite K32 in Hc.
pose proof (crep_slot_geom a G RE X m c (K c) i t (HCall c ltac:(rewrite K32; lia)) ltac:(lia) Ht) as (_ & IB & S32 & SM & SB & AU & MU & k & K0 & K1 & K2).
replace ((i + 1) * class_size c) with (i * class_size c + class_size c) in IB by lia. rewrite K1 in IB, SB.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PH & PHE & RI).
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
rewrite KO in MU. unfold in_iv, in_sh. cbn [fst snd].
assert (SHR : forall z, SH z = z / 8 + 2147450880) by (intros; reflexivity).
assert (HB : reg_beg (ae_L RE) c <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + 3758096384) by lia.
destruct F as [F|[F|[F|[F|[[F NS]|[F NS]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. rewrite RI in F1, F2. rewrite RB in HB. split; [lia|]. rewrite !SHR. Z.div_mod_to_equations. lia.
- pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD. cbn [fst snd] in TD.
unfold prim_lo, prim_hi in *. destruct F as [F1 F2]; cbn [fst snd] in F1, F2. rewrite RB in HB. split; [lia|]. rewrite !SHR. rewrite ?KHI_eq in TK. Z.div_mod_to_equations. lia.
- destruct F as (c' & Hc' & F1 & F2). pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & FB' & _). rewrite FB' in F1, F2. rewrite KS in F2.
rewrite RB in HB. split; [lia|]. rewrite !SHR. Z.div_mod_to_equations. lia.
- destruct F as (c' & Hc' & [F1 F2]). cbn [fst snd] in F1, F2. pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & FB' & _). rewrite FB' in F1, F2. rewrite KS in F2.
rewrite RB in HB. rewrite !SHR in *. split; Z.div_mod_to_equations; lia.
- split.
+ intros Hx. apply NS. exists c, i, t. split; [exact Ht|]. split; [rewrite Hp; reflexivity| exact Hx].
+ destruct F as (c' & Hc' & F1 & F2). pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _). rewrite RB' in F1, F2. rewrite KO in F2.
rewrite RB in HB. rewrite !SHR. Z.div_mod_to_equations. lia.
- split.
+ destruct F as (c' & Hc' & [F1 F2]). cbn [fst snd] in F1, F2. pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _). rewrite RB' in F1, F2. rewrite KO in F2.
rewrite RB in HB. rewrite !SHR in *. Z.div_mod_to_equations. lia.
+ intros Hx. apply NS. exists c, i, t. split; [exact Ht|]. split; [rewrite Hp; reflexivity| exact Hx].
Qed.

Lemma batches_mem_nx_keep : forall (P : Z -> Prop) RE m m' QA bs J fin,
batches_mem_nx RE m QA bs J fin -> Forall bwf bs -> agree_on asegs P m m' -> wmono asegs m m' ->
(forall j x, In j J -> in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x -> P x) ->
batches_mem_nx RE m' QA bs J fin.
Proof.
intros P RE m m' QA bs J fin BM FB AG WM HP. eapply batches_mem_nx_agree; [exact AG| exact BM| | | exact FB].
- apply List.Forall_forall. intros j Hj x Hx. apply (HP j x Hj). left; exact Hx.
- apply List.Forall_forall. intros j Hj x Hx. apply (HP j x Hj). right; exact Hx.
Qed.

Lemma upd_snoc {A} : forall (ws : list A) w v, upd (ws ++ [w]) (length ws) v = ws ++ [v].
Proof. induction ws as [|x ws IH]; intros w v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fold_right_add_app : forall l1 l2, fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma bwf_snoc : forall b p, bwf b -> b_count b < kBatchCount -> 0 <= aptr_req p <= 2^26 ->
bwf (mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + aptr_used p)).
Proof.
intros b p (B1 & B2 & B3 & B4) HC HP. unfold bwf. cbn [b_chunks b_count b_size].
rewrite length_app, map_app, fold_right_add_app. cbn [length fold_right map]. split; [lia|]. split; [lia|]. split; [lia|].
apply Forall_app. split; [exact B4| constructor; [exact HP| constructor]].
Qed.

Lemma bwf_single : forall p, 0 <= aptr_req p <= 2^26 -> bwf (mkB [p] 1 (aptr_used p + kBatchBytes)).
Proof.
intros p HP. unfold bwf. cbn. pose proof kq_consts as (_ & _ & KC & _). rewrite KC. split; [reflexivity|]. split; [lia|]. split; [lia|].
constructor; [exact HP| constructor].
Qed.

Lemma qwf_append_last : forall front b p qb,
qwf (mkQ (front ++ [b]) qb) -> b_count b < kBatchCount -> 0 <= aptr_req p <= 2^26 ->
qwf (mkQ (front ++ [mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + aptr_used p)]) (qb + aptr_used p)).
Proof.
intros front b p qb [HF HB] HC HP. cbn in *. apply Forall_app in HF as [HF1 HF2]. apply Forall_cons_iff in HF2 as [HB2 _].
split.
- apply Forall_app. split; [exact HF1|]. constructor; [apply bwf_snoc; assumption| constructor].
- rewrite map_app, fold_right_add_app in HB. rewrite map_app, fold_right_add_app. cbn [map fold_right b_size q_bytes] in *. lia.
Qed.

Lemma qwf_push_back : forall q b, qwf q -> bwf b -> qwf (q_push_back q b).
Proof.
intros [l qb] b [HF HB] Hb. unfold q_push_back. cbn in *. split.
- apply Forall_app. split; [exact HF| constructor; [exact Hb| constructor]].
- rewrite map_app, fold_right_add_app. cbn. lia.
Qed.
End Mq0.
From stdpp Require gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I QVsB Qsn5 QCiC QQwg QTVW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QTVW.Mq0 QNQk.Mq4 QpY2.Mq8 QpY2.Mq6.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition allocate_entry : Z := 0x3f068.

Definition rz_log (n : Z) : Z :=
if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2
else if n <=? 3968 then 3 else if n <=? 16128 then 4
else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_size_shift : forall n, rz_size n = Z.shiftl 16 (rz_log n).
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); reflexivity. Qed.

Lemma land_mask8 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x - x mod 8)%Z.
Proof.
intros Hx.
assert (E : 18446744073709551608%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3)%Z with 8%Z. pose proof (Z.div_mod x 8). lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition alloc_frame (fj : list byte) (canfill : word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 fj; C8 canfill; C8 (wz 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma alloc_pre1 : forall ra sp gp t0 t1 t2 s0 s1 (canfill : word) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 128 ->
0 <= n < 2^64 -> 0 < tr < 2^64 ->
(forall m1 (u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word) fj,
munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 8) canfill (wz 49) v1 v2 v3 v4 v5 v6 v7
(wz 8) s3 s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) (wz 1) u4 u5 u6 u7)
F (wz 0x3f100) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz tr) (wz 1) canfill a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn Htr CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold allocate_entry.
carve_frame 128%nat ST.
do 14 step.
do 6 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RT0 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]]) end.
step. call0 (asan_inited_spec RE X); [exact RT0| assumption|]. subst.
step. if_lit.
step. call0 (rss_limit_spec RE X); [exact RT0| assumption|]. subst.
step. if_lit.
step. ifz.
stp. step. if_lit.
stp. step. step. if_lit.
stp. stp. step. if_lit.
step. step.
stp. stp. stp.
step. stp. stp. stp.
step.
replace (zxb 3) with (wz 3) by (vm_compute; reflexivity).
stp. stp. stp.
step. step. if_lit.
stp. stp. stp. step. if_lit.
stp. stp.
step. stf.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR].
Qed.

Lemma alloc_rzlog : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n : Z) (Q : machine_state -> Prop),
0 <= n < 2^62 ->
(forall a0', evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (wz (rz_log n)) s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f1d4) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f100) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn CONT. unfold rz_log in CONT.
step. destruct (Z.leb_spec n 48) as [C0|C0]; ifz.
{ stp. step. apply CONT. }
stp. step. destruct (Z.leb_spec n 96) as [C1|C1]; ifz.
{ stp. step. apply CONT. }
stp. step. destruct (Z.leb_spec n 448) as [C2|C2]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 3968) as [C3|C3]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 16128) as [C4|C4]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 32256) as [C5|C5]; ifz.
{ stp. step. apply CONT. }
stp. stp. step.
rewrite v_sltu_b2z. rewrite (unsigned_lit n) by lia. fold_closed_in_goal.
step.
destruct (Z.leb_spec n 64512) as [C6|C6].
- replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. lits. apply CONT.
- replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. lits. apply CONT.
Qed.

Lemma alloc_pre3 : forall ra (sp : word) gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 144 ->
0 <= n -> from_primary n = true ->
(forall m1 (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word),
munch [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 1) (wz (used_size n)) v0 v1 v2 v3 v4 v5 v6 v7
(wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_INSTANCE) (wz tr) (wz (-8)) (wz 7) (wz (A_INSTANCE + 2047)) s11 u4 u5 u6 u7)
F (wz 0x3f2e8) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7
(wz 8) (wz (rz_log n)) s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) s11 t3 t4 t5 t6)
F (wz 0x3f1d4) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn HP CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
apply from_primary_iff in HP. unfold kMaxSize in HP.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2]. pose proof (rz_log_range n) as RL8.
pose proof (rz_size_shift n) as RZS.
assert (N16 : n <= 65536) by (unfold needed in HP; pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)); lia).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 27%nat K27. unfold A_INSTANCE in *.
step.
replace (sx16 (wz 16)) with (wz 16) by (rewrite sx16_any; reflexivity).
step. stp. stp. stp.
step. call_sp (rz_size2log_spec 16); [left; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].
step.
step.
replace (sx16 (wz 2048)) with (wz 2048) by (rewrite sx16_any; reflexivity).
step. stp.
step. call_sp (rz_size2log_spec 2048); [right; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists (v1 : word),
ms1 = MS (@bvmap_set 5 word 10 (wz (Z.max n 8)) (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 19 (wz (rz_log n)) R))) FF (wz 0x3f21c) fcc rv mm ro))
end.
{ step.
assert (NB : rz_log n <> 0 -> 48 < n) by (unfold rz_log; destruct (Z.leb_spec n 48); [intros HH; exfalso; apply HH; reflexivity| lia]).
destruct (Z.eq_dec (rz_log n) 0) as [R0|RP]; ifz.
- step. step. if_lit.
stp. step. step.
destruct (Z.ltb_spec 8 n) as [L8|G8]; ifz.
+ replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R0. reflexivity.
+ stp. replace (Z.max n 8) with 8 by lia. apply evt_done. eexists. simp_regs. rewrite ?R0. reflexivity.
- specialize (NB RP).
step.
destruct (Z.eq_dec (rz_log n) 7) as [R7|R6]; ifz.
+ step.
stp. step. step. ifz.
step.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R7. reflexivity.
+ stp. step. step. ifz.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [v1 ->]. simp_regs.
set (mx := Z.max n 8) in *. assert (MX : 8 <= mx <= 65536) by lia.
step. stp. stp.
stp. stp.
step.
rewrite (unsigned_lit (mx + 7)), land_mask8 by lia.
assert (RU : mx + 7 - (mx + 7) mod 8 = round_up mx 8) by (unfold round_up; Z.div_mod_to_equations; lia).
rewrite RU. pose proof (round_up_8 mx ltac:(lia)) as [RU1 RU2].
stp. step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia. replace (round_up mx 8 + 0) with (round_up mx 8) by lia.
step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia.
replace (Z.land (round_up mx 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
step. if_lit.
assert (NE : needed n = round_up mx 8 + rz_size n) by (unfold needed; reflexivity).
stp. step. stp.
step.
replace (wz (bv_swrap 32 (Z.shiftl 16 (bv_unsigned (wz (rz_log n)) mod 32)))) with (wz (rz_size n)).
2:{ rewrite (unsigned_lit (rz_log n)), Z.mod_small, <- RZS by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia. }
replace (v_sltiu (wz n) 1) with (wz (if n =? 0 then 1 else 0))
by (unfold v_sltiu; rewrite (unsigned_lit n) by lia; change (bv_wrap 64 1) with 1; destruct (Z.eqb_spec n 0), (Z.ltb_spec n 1); try reflexivity; lia).
stp.
step.
replace (n + (if n =? 0 then 1 else 0)) with (used_size n) by (unfold used_size; destruct (Z.eqb_spec n 0); lia).
step.
step.
rewrite <- NE.
step.
try (match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end).
rewrite !v_sltu_b2z. rewrite (unsigned_lit (needed n)) by lia. fold_lit_ux.
replace (needed n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
stp. stp. stp. stp.
step.
rewrite Z.land_0_l. replace (0 + needed n) with (needed n) by lia.
assert (US : 1 <= used_size n <= 65537) by (unfold used_size; lia).
step. ifz.
step. ifz.
step.
step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST].
Qed.
End S.
End Mq1.
From Stdlib Require Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZbm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QNQk.Mq1 QUnM QZbm QTVW.Mq3 QpY2.Mq7 QpY2.Mq5.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition amemset_entry : Z := 0x61be0.
Definition amemset_frame : Z := 2128.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(dst c n lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (b8 c) (Z.to_nat n))].

Lemma u_nm65 : forall n, 1 <= n <= 64 -> bv_unsigned (wz (n + -65)) = 18446744073709551551 + n.
Proof. intros n Hn. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

Lemma rw_cells_below : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.

Lemma shadow_ok_zrd_head : forall m dst n, shadow_ok m dst n -> 0 < n -> zrd m (SH dst) (SH (dst + n - 1) - SH dst).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO i ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH dst + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma qslow_loop : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x61dac) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x61d9c) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR A0 C1 C2 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 1) e) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. replace (p + 1) with e by lia. apply K.
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Ltac amemset_finish FR ST usp c :=
do 9 step; release_frame FR ST usp; step;
apply evt_done; unfold amemset_post; do 15 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|];
lazymatch goal with H : rw_cells _ _ _ [CB _ (repeat _ _)] |- _ => rewrite (Z.mod_small c 256) in H by lia; exact H end.

Lemma amemset_core : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst c n lo : Z) (old : list byte) (w1 w2 : word),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 4096 ->
0 <= c < 256 -> 0 < n <= 2^43 -> appr dst n -> dst + n <= band_lo ->
rw_cells asegs m dst [CB (Z.to_nat n) old] ->
shadow_ok m dst n ->
(n <= 64 -> rw_cells asegs m (8 * (SH dst / 8)) [C8 w1] /\ rw_cells asegs m (8 * (SH (dst + n - 1) / 8)) [C8 w2]) ->
evt asegs (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz amemset_entry) fc None m (seg_rom asegs)).
Proof.
intros until w2; intros RT RL MI ST CEIL LO HC [N0 N43] K1d K2d RC SO NB.
pose proof CEIL as CEIL'. idtac. pose proof K2d as K2d'.
apply appr_to_lia in K1d; [| lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(dst, dst + n); (lo, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold amemset_entry.
carve_frame 2128%nat ST.
do 10 istep.

rt_now RT RL 42%nat K42. rt_now RT RL 40%nat K40.
step. stp. stp. step. ifz. clear K42 K40.

stp. step. step. step.
rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

stp. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct (NB N64) as [W1 W2].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W1; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]];
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W2; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]] end.
rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5.
step. stp. step. stp. stp. step. stp. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x61c70) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.

rt_now RT RL 23%nat K23. step. stp. step. clear K23 K19 K5.
clear MUs. call_u memset_spec. { rewrite ?unsigned_lit by lia. exact RC. } { assumption. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
amemset_finish FR ST' (bv_unsigned sp) c.
-
ifz. step. ifz.
step. step. step. step. step.
call_u rip_spec_lh; [rt_solve RT RL| exact RL| assumption| unsigned_lits; exact ST| exact CEIL'| unsigned_lits; lia| exact SO'| lia| rewrite ?KHI_eq; lia|].
match goal with H : RTconst RE X ?mc |- evt _ _ (MS _ _ _ _ _ ?mc' _) => constr_eq mc mc'; rename H into RT1 end.
step. step. step. step. step. ifz.

rtc RT1 23%nat K23. step. stp. step. clear K23.
clear MUs. call_u memset_spec. { rewrite ?unsigned_lit by lia. exact RC. } { assumption. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
amemset_finish FR ST' (bv_unsigned sp) c.
Qed.

End S.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.
Hypothesis HRP : forall a G RE X m, ac_RPrim C a G RE X m <-> RPrim a G RE X m.
Hypothesis HRC : forall a LB G RE X m, ac_RChunks C a LB G RE X m <-> RChunks a LB G RE X m.
Hypothesis HRQ : forall a LB G RE X m, ac_RQuar C a LB G RE X m <-> RQuar a LB G RE X m.
Hypothesis HRF : forall FS RE X m, ac_RFake C FS RE X m <-> RFake FS RE X m.

Lemma asan_memset_A : aasan_memsetA_stmt asegs a_alayout (ARUN C).
Proof.
unfold aasan_memsetA_stmt. intros until lo; intros old s LB FS RE AR ST CEIL LO MI Ha0 Ha1 Ha2 HC HN RC SB SHD K1 K2 WH.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof AX as (GC & R1 & _ & R3 & R4 & _ & R6 & _ & R8).
pose proof (proj1 GC) as RL.
apply HRT in R1. apply HRP in R3. apply HRC in R4. apply HRQ in R6. apply HRF in R8.
subst a0 a1 a2. cbn [ala_asan_memset ala_memset_stack a_alayout] in *.

assert (WH0 : 64 < n <= 2^43 \/ amemset_whereA LB0 FS0 dst n).
{ destruct WH as [W|[(p & A & n0 & Hin & W)|(cl & f & Hin & W)]]; [left; exact W| right; left| right; right].
- exists p, A, n0. split; [eapply Permutation_in; [exact PB| exact Hin]| exact W].
- exists cl, f. split; [eapply Permutation_in; [exact PF| exact Hin]| exact W]. }
assert (N43 : 0 < n <= 2^43).
{ destruct WH0 as [W|[(p & A & n0 & Hin & W)|(cl & f & Hin & W)]]; [lia| |].
- pose proof (gc_block_small _ _ _ _ _ _ GC p A n0 Hin). lia.
- destruct R8 as (_ & _ & _ & [SHf _] & _). destruct (SHf _ Hin) as (Hc & _). cbn [ff_cls fst] in Hc. unfold kFsClasses in Hc.
unfold ff_size in W. assert (2 ^ cl <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). lia. }
assert (NB : exists w1 w2 : word, n <= 64 ->
rw_cells asegs m (8 * (SH dst / 8)) [C8 w1] /\ rw_cells asegs m (8 * (SH (dst + n - 1) / 8)) [C8 w2]).
{ destruct (Z_le_gt_dec n 64) as [LE|GT].
- destruct WH0 as [W|W]; [lia|].
destruct (amemset_nbhd _ LB0 FS0 G RE X m GC R3 R4 R6 R8 dst n W ltac:(lia)) as [J1 J2].
destruct (hjunk_C8 m _ J1) as [w1 Hw1]. destruct (hjunk_C8 m _ J2) as [w2 Hw2].
exists w1, w2. intros _. split; [exact Hw1| exact Hw2].
- exists (wz 0), (wz 0). intros LE. lia. }
destruct NB as (w1 & w2 & NB).
eapply (amemset_core RE X); try eassumption; try lia.
Qed.
End Lift.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUvT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QUvT QsGW QDw3 QNwL QYnC QSsj Qu1d QNQk.Mq4 QNQk.Mq2 QZbm QpY2.Mq9 QpY2.Mq4.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc0_entry : Z := 0x4a790.
Definition fsmalloc9_entry : Z := 0x4a904.
Definition fsmalloc_stack : Z := 48 + tls_fs_stack.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma filter_cls_length : forall c FS0,
length (filter (fun f : fframe => ff_cls f =? c) FS0) = length (List.filter (fun f => ff_cls f =? c) FS0).
Proof.
intros c FS0. induction FS0 as [|f l IH]; [reflexivity|]. rewrite filter_cons. cbn [List.filter].
destruct (decide _) as [D|D]; destruct (ff_cls f =? c) eqn:E.
- cbn [length]. rewrite IH. reflexivity.
- exfalso. exact D.
- exfalso. apply D. exact I.
- exact IH.
Qed.

Lemma land_16383 : forall x, Z.land x 16383 = x mod 16384.
Proof. intros x. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod16384_of_64 : forall x, (x mod 2^64) mod 16384 = x mod 16384.
Proof. intros x. apply Z.mod_mod_divide. exists (2^50); reflexivity. Qed.

Lemma fs0_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 4096) fl -> fl = flags_of FS0 FS 0 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 0) FS0)) < fs_N 0 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (16384 - i) -> 0 <= i < 16384 ->
bv_unsigned cur mod 16384 = (u + i) mod 16384 ->
(forall j, 0 <= j < i -> live_b FS0 0 (fs_frame FS 0 ((u + j) mod 16384)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (16384 - i')) (wz (FS + 4096)) cur' (wz 16383) a4
(wz (FS + 4096 + pos)) (wz pos) (wz 0) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4a88c) fc None mc (seg_rom asegs)
/\ 0 <= pos < 16384 /\ live_b FS0 0 (fs_frame FS 0 pos) = false /\ 0 <= i' < 16384)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (16384 - i)) (wz (FS + 4096)) cur (wz 16383) a4 a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4a814) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 16383).
assert (Hpos : pos = (u + i) mod 16384) by (subst pos; rewrite land_16383; exact Hcur).
assert (PR : 0 <= pos < 16384) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 0 (fs_frame FS 0 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 4096) fl pos (b8 1) (wa (FS + 4096 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 16384) as [LT|GE].
+ if_true_u. replace (16384 - i + -1) with (16384 - (i + 1)) by lia.
eapply (IH (Z.to_nat (16384 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod16384_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 0 -> live_b FS0 0 (fs_frame FS 0 p) = true).
{ apply (scan_exhausts FS0 FS 0 u (i + 1)); try change (fs_N 0) with 16384; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 0 ltac:(lia) ALL) as CNT. change (fs_N 0) with 16384 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 4096) fl pos (b8 0) (wa (FS + 4096 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 16383), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc0_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 0) FS0)) < fs_N 0 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 0 pos /\ 0 <= pos < fs_N 0 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 0 f
/\ RTconst RE X m' /\ RFake ((0, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 0 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS, FS + 8); (fs_flag FS 0 pos, fs_flag FS 0 pos + 1);
(f, f + ff_size 0); (SH f, SH f + ff_size 0 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc0_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc0_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 0 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. rewrite Z.mul_0_r, Z.add_0_r in HINT.
pose proof (FL 0 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 0) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 16384) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 0 0) with (FS + 4096) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x553c0.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4a814.

eapply evt_cut.
{ eapply (fs0_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS, FS + 8); (FS + 4096 + pos, FS + 4096 + pos + 1);
(FS + 36864 + pos * 64, FS + 36864 + pos * 64 + 64); (SH (FS + 36864 + pos * 64), SH (FS + 36864 + pos * 64) + 8)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 4 istep. rewrite (unsigned_lit pos), Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 4096) fl pos (wa (FS + 4096 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 4096) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 3 istep.
remember (FS + 36864 + pos * 64) as f eqn:Ef in *.
assert (FB : FS + 36864 <= f /\ f + 64 <= FS + 36864 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 64) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 64 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 64) = SH f + 8) by (rewrite !SH_eq; replace (f + 64) with (f + 8 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 64) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 8) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
destruct (hjunk_cells _ (SH f) 8 J2f) as [junks SHC]. clear J2c J2r J2f.
istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 24 (take 24 (drop 32 junkf))] [C8 (wz (FS + 4096 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 56 (take 24 junkf ++ le8 sp ++ take 24 (drop 32 junkf))] [C8 (wz (FS + 4096 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 0 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 0 pos = FS + 4096 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 0 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 0) with 16384; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 0) with 64 in NT. change (64 / 8) with 8 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. rewrite Z.mul_0_r, Z.add_0_r. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 0 - 8) with (f + 56) by (change (ff_size 0) with 64; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 24 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 0) with 16384; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 0) with 64. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split; [exact SHC|].
rewrite FLG. change (ff_size 0) with 64. change (64 / 8) with 8. exact MU2.
Qed.

End Walk.
End Mq3.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTa Q0z1 QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.

Import Qc27 QdTa Q0z1 QwAs.Mq2.
Import QvG1 QNwL QNQk.Mq1 QpY2.Mq2 QcfN.Mq1. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module LF.
Import Ltac2.

Ltac2 is_enc_atom (a : constr) : bool :=
match Constr.Unsafe.kind a with
| Constr.Unsafe.App f _ =>
if Constr.equal f constr:(zhigh) then true else if Constr.equal f constr:(zhull) then true
else Constr.equal f constr:(zsel)
| _ => false
end.
Ltac2 rel_prune_gen (sec : bool) (hops : int) (cap : int) (disj : bool) : unit :=
let ops := RL.ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if Bool.or sec (RL.is_local id) then (if SF2.arith_logic ty then Some (id, ty) else None) else None
end) hs in

let lets := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some b => Some (RL.add_atom (Control.hyp id) (RL.atoms ops [] b))
| None => None
end) hs in
let step g := List.fold_left (fun acc ap => if RL.meets ap g then List.fold_left (fun acc a => RL.add_atom a acc) acc ap else acc) g
(List.append lets (List.map (fun f => let (_, p) := f in RL.atoms ops [] p) facts)) in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in
let g0 := RL.atoms ops [] (Control.goal ()) in

let g0 := match g0 with
| [] => List.fold_left (fun g f => let (_, p) := f in List.fold_left (fun g a => RL.add_atom a g) g (RL.atoms ops [] p))
[] (List.firstn (if Int.le (List.length facts) 4 then List.length facts else 4) (List.rev facts))
| _ :: _ => g0
end in
let g := close hops g0 in

let drop := List.map_filter (fun f => let (id, p) := f in
let ap := RL.atoms ops [] p in
if List.exist is_enc_atom ap then Some id
else if Bool.or disj (SF2.plain_arith true p) then (if RL.meets ap g then None else Some id)
else Some id) facts in
let ndisj := List.length (List.filter (fun f => let (id, p) := f in
if List.exist (fun d => Ident.equal d id) drop then false else Bool.neg (SF2.plain_arith true p)) facts) in
if Int.gt (Int.sub (List.length facts) (List.length drop)) cap then Control.zero (Tactic_failure None) else
if Int.gt ndisj 4 then Control.zero (Tactic_failure None) else
match drop with [] => () | _ :: _ => Std.clear drop end.
Ltac rel_prune_local2 := ltac2:(Control.enter (fun () => rel_prune_gen false 2 100000 false)).
Ltac rel_prune_local4 := ltac2:(Control.enter (fun () => rel_prune_gen false 4 100000 false)).
Ltac rel_prune_sec2 := ltac2:(Control.enter (fun () => rel_prune_gen true 2 100000 false)).
Ltac rel_prune_sec4 := ltac2:(Control.enter (fun () => rel_prune_gen true 4 100000 false)).
Ltac rel_prune_disj2 := ltac2:(Control.enter (fun () => rel_prune_gen false 2 30 true)).
Ltac rel_prune_disj4 := ltac2:(Control.enter (fun () => rel_prune_gen false 4 45 true)).

Ltac2 zlf_arith_goal () : unit := if SF2.arith_logic (Control.goal ()) then () else Control.zero (Tactic_failure None).
Ltac zlf_arith_goal := ltac2:(Control.enter zlf_arith_goal).

Ltac2 zlf_no_enc () : unit :=
let ops := RL.ops () in
if List.exist (fun h => let (_, body, ty) := h in
match body with
| Some _ => false
| None => if SF2.arith_logic ty then List.exist is_enc_atom (RL.atoms ops [] ty) else false
end) (Control.hyps ())
then Control.zero (Tactic_failure None) else ().
Ltac zlf_no_enc := ltac2:(Control.enter zlf_no_enc).
End LF.
Ltac zlf_no_enc := LF.zlf_no_enc.
Ltac zlf_arith_goal := LF.zlf_arith_goal.
Ltac rel_prune_local2 := LF.rel_prune_local2.
Ltac rel_prune_local4 := LF.rel_prune_local4.
Ltac rel_prune_sec2 := LF.rel_prune_sec2.
Ltac rel_prune_sec4 := LF.rel_prune_sec4.
Ltac rel_prune_disj2 := LF.rel_prune_disj2.
Ltac rel_prune_disj4 := LF.rel_prune_disj4.

Ltac zify_goal_dm :=
repeat match goal with
| |- context [Z.div ?x ?y] => zify_new_dm x y
| |- context [Z.modulo ?x ?y] => zify_new_dm x y
end.
Ltac goal_has_dm := match goal with |- context [Z.div _ _] => idtac | |- context [Z.modulo _ _] => idtac end.

Definition zlf_done (x y : Z) : Prop := True.
Lemma zlf_div_spec : forall x d, 0 < d -> d * (x / d) <= x < d * (x / d) + d.
Proof. intros x d Hd. pose proof (Z.div_mod x d ltac:(lia)). pose proof (Z.mod_pos_bound x d Hd). lia. Qed.
Lemma zlf_mod_spec : forall x d, 0 < d -> x = d * (x / d) + x mod d /\ 0 <= x mod d < d.
Proof. intros x d Hd. split; [apply Z.div_mod; lia| apply Z.mod_pos_bound; exact Hd]. Qed.
Ltac zlf_pos_lit y := lazymatch y with Zpos _ => idtac end.
Ltac zlf_new x y :=
lazymatch goal with
| _ : zlf_done x y |- _ => fail
| _ => zlf_pos_lit y; pose proof (zlf_div_spec x y eq_refl); pose proof (zlf_mod_spec x y eq_refl); pose proof (I : zlf_done x y)
end.
Ltac zify_divlit :=
repeat match goal with
| |- context [Z.div ?x ?y] => zlf_new x y
| |- context [Z.modulo ?x ?y] => zlf_new x y
| _ : context [Z.div ?x ?y] |- _ => zlf_new x y
| _ : context [Z.modulo ?x ?y] |- _ => zlf_new x y
| _ := context [Z.div ?x ?y] |- _ => zlf_new x y
| _ := context [Z.modulo ?x ?y] |- _ => zlf_new x y
end.

Ltac zlf_prune2 := rel_prune_local2.
Ltac zlf_prune4 := rel_prune_local4.
Ltac lia_pruned := zlf_arith_goal; first [ Qo9G.term_slim ltac:(zlf_prune2; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| zlf_prune4;
first [ Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zlf_no_enc; zify_divlit; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ] ].

Ltac lia_fast := first [ lia_pruned
| zify_prune;
first [ Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_has_divmod; Zify.zify; xlia zchecker) ]
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Ltac tslia_fast := first [ exact I
| sf_unhide; lia_pruned
| Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Q0z1.tslia ].

Ltac solve_cond_base_p :=
first [ reflexivity
| apply Z.ltb_lt; lia_pruned | apply Z.ltb_ge; lia_pruned
| apply Z.leb_le; lia_pruned | apply Z.leb_gt; lia_pruned
| apply Z.eqb_eq; lia_pruned | apply Z.eqb_neq; lia_pruned ].
Ltac solve_cond_rec_p :=
lazymatch goal with
| |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec_p
| |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec_p
| _ => solve_cond_base_p
end.
Ltac solve_cond_p := unfold_cond; fold_lit_ux; solve_cond_rec_p.
Ltac if_true_p :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond_p]
end.
Ltac if_false_p :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond_p]
end.

Ltac zlf_no_vars c := match c with context [?x] => is_var x; fail 1 | _ => idtac end.
Ltac if_true_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
zlf_no_vars c; replace c with true; [cbv iota| symmetry; unfold_cond; fold_lit_ux; reflexivity]
end.
Ltac if_false_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
zlf_no_vars c; replace c with false; [cbv iota| symmetry; unfold_cond; fold_lit_ux; reflexivity]
end.
Ltac if_lit_fast := first [ if_true_lit | if_false_lit | if_true_p | if_false_p | if_true | if_false ].

Ltac sfp_fast := first [ apply Z.le_refl | lia_pruned ].

Ltac lia_pruned_disj := zlf_arith_goal;
first [ Qo9G.term_slim ltac:(rel_prune_disj2; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(rel_prune_disj4; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ].

Ltac st_avoid_solve_fast :=
lazymatch goal with
| |- st_avoid (?lo, _) =>
lazymatch lo with
| context [rl_T _] => eapply st_avoid_T; [eassumption| cbn [fst snd]; first [ lia_pruned | lia ]| cbn [fst snd]; first [ lia_pruned | lia ]]
| _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; first [ lia_pruned | unfold prim_lo, prim_hi in *; lia ]
end
| |- _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; first [ lia_pruned | unfold prim_lo, prim_hi in *; lia ]
end.

Ltac if_lit_lit := first [ if_true_lit | if_false_lit | if_true | if_false ].

Ltac addr_eq_tac_w :=
lazymatch goal with
| |- @eq nat _ _ => fail
| |- _ => symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
end.

Module SF2L.
Import Ltac2.
Ltac2 rec clean2 (bad : constr list) (kd : constr list) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) kd then
(if Int.equal (Array.length args) 2 then
(match Q0z1.SF2.vars_of [] (Array.get args 1) with
| [] => clean2 bad kd (Array.get args 0) | _ :: _ => false end)
else false)
else if List.exist (Constr.equal f) bad then false
else if clean2 bad kd f then Array.fold_left (fun b a => if b then clean2 bad kd a else false) true args else false
| Constr.Unsafe.Constant _ _ => if List.exist (Constr.equal c) bad then false else true
| Constr.Unsafe.Prod b body => if clean2 bad kd (Constr.Binder.type b) then clean2 bad kd body else false
| Constr.Unsafe.Lambda _ _ => false
| Constr.Unsafe.Case _ _ _ _ _ => false
| Constr.Unsafe.LetIn _ _ _ => false
| _ => true
end.
Ltac2 hide_poison2 () : unit :=
let bad := Q0z1.SF2.bad_heads () in
let kd := [constr:(Z.div); constr:(Z.modulo)] in
let kk := Q0z1.SF2.sk_mk () in
List.iter (fun h => let (id, body, ty) := h in
match body with
| Some _ => ()
| None =>
if Q0z1.SF2.al_k kk ty then
(if (if Q0z1.SF2.plain_k kk false ty then clean2 bad kd ty else false) then ()
else let c := Control.hyp id in
ltac1:(c |- lazymatch type of c with ?T => change T with (Q0z1.sf_hide T) in c end) (Ltac1.of_constr c))
else ()
end) (Control.hyps ()).
Ltac2 hide_poison2_1 () : unit := Control.enter hide_poison2.
End SF2L.
Ltac sf_hide_poison_divlit := ltac2:(SF2L.hide_poison2_1 ()).
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOJv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QvG1 QyW2 QsGW Qp4j QDw3 QUxU QNwL QYnC QSsj Qu1d QNQk.Mq1 QpY2.Mq1 QTVW.Mq0 QNQk.Mq4 QOJv.Mq3.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition mmap_or_die_entry : Z := 0x7703c.
Definition MMAPANON_STACK : Z := 320.

Lemma apply_unit_writes : forall ws m lo,
(forall w, In w ws -> length (snd w) = 1%nat) ->
map (fun w => bv_unsigned (fst w)) ws = zrange lo (length ws) ->
0 <= lo -> lo + Z.of_nat (length ws) <= 2^64 ->
(forall x : word, lo <= bv_unsigned x < lo + Z.of_nat (length ws) -> exists b, apply_writes m ws x = Some b)
/\ (forall x : word, ~ (lo <= bv_unsigned x < lo + Z.of_nat (length ws)) -> apply_writes m ws x = m x).
Proof.
induction ws as [|[aw bs] ws IH]; intros m lo Hu Hm Hlo Hhi; cbn [apply_writes length map zrange] in *.
- split; [intros x Hx; lia| intros x _; reflexivity].
- injection Hm as Haw Hm. cbn [fst snd] in *.
pose proof (Hu (aw, bs) ltac:(left; reflexivity)) as Hl. cbn [snd] in Hl.
destruct bs as [|b [|b' bs]]; try discriminate.
assert (Eaw : aw = wa lo) by (apply bv_eq; rewrite wa_unsigned by lia; exact Haw).
destruct (IH (write_to_mem m aw [b]) (lo + 1) ltac:(intros w Hw; apply Hu; right; exact Hw) Hm ltac:(lia) ltac:(lia)) as [IH1 IH2].
assert (W1 : forall x : word, write_to_mem m aw [b] x = if bv_unsigned x =? lo then Some b else m x).
{ intros x. rewrite Eaw. rewrite (write_to_mem_spec [b] m lo x) by (cbn [length]; lia). cbn [length].
pose proof (bv_unsigned_in_range 64 x).
destruct (Z.eqb_spec (bv_unsigned x) lo) as [E|NE].
- rewrite E. replace ((lo <=? lo) && (lo <? lo + Z.of_nat 1)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
rewrite Z.sub_diag. reflexivity.
- destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + Z.of_nat 1)) eqn:C; [| reflexivity].
apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia. }
split.
+ intros x Hx. destruct (Z.eq_dec (bv_unsigned x) lo) as [E|NE].
* rewrite (IH2 x) by lia. rewrite W1, E, Z.eqb_refl. exists b. reflexivity.
* apply IH1. lia.
+ intros x Hx. rewrite (IH2 x) by lia. rewrite W1. destruct (Z.eqb_spec (bv_unsigned x) lo); [lia| reflexivity].
Qed.

Lemma zrange_length : forall lo k, length (zrange lo k) = k.
Proof. intros lo k. revert lo. induction k; intros; cbn; [reflexivity| rewrite IHk; reflexivity]. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma sh_lo_SH a : QKTr.sh_lo a = SH a.
Proof. unfold QKTr.sh_lo, SH, kShadowOffset, A_SHADOW_OFS. lia. Qed.
Lemma sh_hi_SH a n : a mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> QKTr.sh_hi a n = SH a + n / 8.
Proof. intros Ha Hn Hp. unfold QKTr.sh_hi, SH, kShadowOffset, A_SHADOW_OFS. Z.div_mod_to_equations. lia. Qed.

Definition map_anon_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(N : Z) (avoid : list (Z * Z)) (lo : Z) (m : mem) (ans : ansA) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ match ans with
| AErr => a0 = wz 0 /\ munch [(bv_unsigned sp - MMAPANON_STACK, bv_unsigned sp)] m m'
| AOk mb => a0 = wz mb
/\ mb mod 4096 = 0 /\ appr mb N /\ mb + N <= band_lo /\ avoids mb N avoid = true
/\ munch [(bv_unsigned sp - MMAPANON_STACK, bv_unsigned sp); (mb, mb + N); (SH mb, SH mb + N / 8)] m m'
/\ rw_cells asegs m' mb [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
/\ (exists shj, rw_cells asegs m' (SH mb) [CB (Z.to_nat (N / 8)) shj])
end.

Lemma mmap_or_die_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (N lo : Z) (avoid : list (Z * Z)) (name : word),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPANON_STACK ->
N mod 4096 = 0 -> 0 < N -> N <= 2^40 ->
(forall b, (0 < b /\ b + N <= 2^64) -> avoids b N avoid = true -> appr b N /\ b + N <= band_lo) ->
(forall b o, (0 < b /\ b + N <= 2^64) -> avoids b N avoid = true -> In o (rlay_objs RE X) -> b + N <= fst o \/ fst o + snd o <= b) ->
impl asegs atn (enode (NMmap 0 N PROT_RW FL_ANON) (dec_anonA N avoid))
(epost (map_anon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N avoid lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz N) name a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mmap_or_die_entry) fc None m (seg_rom asegs)).
Proof.
intros until name; intros RT RL MI ST CEIL LO NAL N0 N40 AVK AVO.
pose proof CEIL as CEIL'. idtac. unfold MMAPANON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. unfold mmap_or_die_entry.
apply impl_enode.
carve_frame 48%nat ST.
do 5 step.
step. step. step. step.
step.
clear K18 K8.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. stf. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec _ _); try eassumption; [lia|]. subst. clear RT1. rename POST into RT1.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|mb].
-
apply dec_anonA_err_inv in Hdec. subst rsp. sys_nret.
change (errno_ret ENOMEM) with (wz (-12)).
step.
step. step. step.
stp. stp. step. if_lit.
step. if_lit.
stp. step.
step. step. stf. step.
step. step.
stp. stp. step. if_lit.
step.
unfold_cond. rewrite (unsigned_lit (bv_unsigned sp + -40)) by lia. if_lit.
stp. stp.
stp. step.
step. if_lit.
stp. step. step. if_lit.
step. step.
step. do 4 step. step. step.
release_frame FR ST (bv_unsigned sp). clear RT1.
apply evt_done. unfold map_anon_post. do 16 eexists. split; [reflexivity|].
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| split; [reflexivity| exact MU]].
eapply RTconst_munch; [exact RT| exact MU| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor].
-
apply dec_anonA_ok_inv in Hdec as (ws & -> & Emb & GOK & AV & WS & COV).
rewrite (mmap_len_aligned N) in * by exact NAL.
cbn [eff_ret] in Emb. pose proof (bv_unsigned_in_range 64 (wz mb)) as MBR. unfold bv_modulus in MBR. change (2 ^ Z.of_N 64) with (2^64) in MBR. rewrite <- Emb in MBR.
unfold grant_ok in GOK. apply andb_prop in GOK as [GOK G3]. apply andb_prop in GOK as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1. idtac.
rewrite sh_lo_SH in COV. rewrite (sh_hi_SH mb N) in COV by (try lia; Z.div_mod_to_equations; lia).
replace (SH mb + N / 8 - SH mb) with (N / 8) in COV by lia.
assert (LWS : length ws = Z.to_nat (N / 8)) by (rewrite <- (zrange_length (SH mb)), <- COV, length_map; reflexivity).
rewrite (mmap_len_aligned N) in G3 by exact NAL. destruct (AVK mb ltac:(rewrite grant_ceil_val in G3; lia) AV) as [GK GB]. apply appr_to_lia in GK; [| lia| lia].
assert (SHB : 0x7fff8000 <= SH mb /\ SH mb + N / 8 <= 0x10007fff8000) by (clear -G1 G2 G3 N0 GB; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
sys_nret.
lazymatch goal with |- context [apply_unmaps ?mm []] => change (apply_unmaps mm []) with mm end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_writes (apply_zeros ?mz [(?A1, wz ?n1)]) ws) _) =>
change (apply_zeros mz [(A1, wz n1)]) with (apply_zeros mz [(wa mb, wz N)]);
assert (Hza : 0 <= mb < 2^64) by lia; assert (Hzn : 0 <= N < 2^64) by lia; assert (Hzan : mb + N <= 2^64) by lia;
apply (munch_weaken _ [(bv_unsigned sp - 320, bv_unsigned sp); (mb, mb + N); (SH mb, SH mb + N / 8)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto];
transport_zeros asegs mz mb N Hza Hzn Hzan;
pose proof (rw_cells_zeros_new asegs mz mb N Hza Hzn Hzan) as ZNEW;
remember (apply_zeros mz [(wa mb, wz N)]) as m2 eqn:Heqm; clear Heqm Hza Hzn Hzan
end.
Unshelve. 2: (apply a_ro_addr_false; lia).

destruct (apply_unit_writes ws m2 (SH mb) ltac:(intros w Hw; unfold wshape_ok in WS; rewrite forallb_forall in WS;
pose proof (WS w Hw) as B; apply andb_prop in B as [_ B]; apply Nat.eqb_eq in B; exact B)
ltac:(rewrite LWS; exact COV) ltac:(lia) ltac:(rewrite LWS, Z2Nat.id by lia; lia)) as [PRES SAME].
rewrite LWS, Z2Nat.id in PRES, SAME by lia.
assert (MU23 : munch [(SH mb, SH mb + N / 8)] m2 (apply_writes m2 ws)) by (intros xw Hx; apply SAME; cbn [outside] in Hx; lia).
assert (WM23 : wmono asegs m2 (apply_writes m2 ws)).
{ intros xw Hx. pose proof (bv_unsigned_in_range 64 xw) as XR.
destruct (Z.lt_ge_cases (bv_unsigned xw) (SH mb)) as [L1|L1]; [unfold wview in *; rewrite SAME by lia; exact Hx|].
destruct (Z.lt_ge_cases (bv_unsigned xw) (SH mb + N / 8)) as [L2|L2]; [| unfold wview in *; rewrite SAME by lia; exact Hx].
destruct (PRES xw ltac:(lia)) as [b Hb]. unfold wview. rewrite Hb. discriminate. }
lazymatch goal with H : mem_inv asegs m2 |- _ =>
assert (MI3 : mem_inv asegs (apply_writes m2 ws));
[ intros xw b Hb; pose proof (bv_unsigned_in_range 64 xw) as XR;
destruct (decide (SH mb <= bv_unsigned xw < SH mb + N / 8)) as [IN|OUT];
[ apply a_ro_addr_false; lia | rewrite SAME in Hb by exact OUT; exact (H xw b Hb) ]
| clear H ] end.
transport_after_call asegs m2 (apply_writes m2 ws) MU23 WM23.
assert (SHJ : hjunk (apply_writes m2 ws) (SH mb) (SH mb + Z.of_nat (Z.to_nat (N / 8)))).
{ rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros y Hy. destruct (PRES (wa y) ltac:(rewrite wa_unsigned by lia; lia)) as [b Hb]. exists b. exact Hb. }
destruct (hjunk_cells _ _ _ SHJ) as [shj SHC]. clear SHJ.
remember (apply_writes m2 ws) as m3 eqn:Heqm3. clear Heqm3 PRES SAME MU23 WM23.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite <- ?Emb, ?(unsigned_lit mb) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit mb) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? mb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit mb) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit mb) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? mb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [| constructor; [| constructor]]].
- intros y Hy Fy. cbn [fst snd] in Hy. destruct (fp_RTconst_where RE X y Fy) as [LOW|(o & Ho & [O1 O2])]; [lia|].
destruct (AVO mb o ltac:(lia) AV Ho); lia.
- intros y Hy Fy. cbn [fst snd] in Hy. destruct (fp_RTconst_where RE X y Fy) as [LOW|(o & Ho & [O1 O2])]; [lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & OK & _). rewrite ?KHI_eq in OK. lia. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 4 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_anon_post. do 16 eexists. split; [first [reflexivity| rewrite <- Emb; reflexivity]|].
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT2|].
split; [first [reflexivity| rewrite <- Emb; reflexivity]|]. split; [exact G1|]. split; [apply appr_of_lia; exact GK|]. split; [exact GB|]. split; [exact AV|].
split; [exact MU|]. split; [exact ZNEW| exists shj; exact SHC].
Qed.
End S.
End Mq5.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QKTr.
Import QJBH.
Import QvG1 QyW2 Qp4j QDw3 QNwL QYnC QSsj QNQk.Mq1 QTVW.Mq0 QOJv.Mq4.
Import QlES. Local Ltac QsGW.small_offset k ::= QsGW.mkr__small_offset_0 k. Local Ltac QoSL.solve_load ::= QsGW.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition PZ_STACK : Z := 640.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition pz_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr size lo : Z) (m : mem) (s : PStateA) (r : unit) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch [(bv_unsigned sp - PZ_STACK, bv_unsigned sp); (SH addr, SH addr + size / 8)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ rw_cells asegs m' (SH addr) [CB (Z.to_nat (size / 8)) (repeat (b8 0) (Z.to_nat (size / 8)))].

Definition poison_zero_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> KHI <= addr -> addr + size <= 2^47 ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
End S.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg QbcP_c1 Q61C QWRO Qu4g QFQR QKBN QN4c QXcn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2 QDM6 QUcd QJFf QBrp.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QmP7.Mq1.
Import QXcn.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Lemma zbytes_bound : forall m A n, zbytes m A n -> 0 <= A /\ A + n <= 2^64.
Proof. intros m A n [[H1 [H2 _]] _]. lia. Qed.

Lemma zbytes_store_ok : forall m A n i (j : nat),
zbytes m A n -> 0 <= i -> i + Z.of_nat j <= n -> store_ok asegs m (wa (A + i)) j = true.
Proof. intros m A n i j [W _] Hi Hj. eapply wr_at_store_ok; eauto. Qed.

Lemma zbytes_store_ok_at : forall m A n a (j : nat),
zbytes m A n -> A <= a -> a + Z.of_nat j <= A + n -> store_ok asegs m (wa a) j = true.
Proof. intros m A n a j ZB H1 H2. replace a with (A + (a - A)) by lia. eapply zbytes_store_ok; [exact ZB| lia| lia]. Qed.

Lemma zbytes_write : forall m A n i bs,
zbytes m A n -> 0 <= i -> i + Z.of_nat (length bs) <= n -> Forall (fun b => b = b8 0) bs ->
zbytes (write_to_mem m (wa (A + i)) bs) A n.
Proof.
intros m A n i bs Z0 Hi Hn Hbs. pose proof (zbytes_bound _ _ _ Z0) as [B1 B2]. destruct Z0 as [W Z0]. split.
- apply wr_at_write. exact W.
- intros k Hk.
destruct (Z.lt_ge_cases k i) as [L|GE]; [| destruct (Z.lt_ge_cases k (i + Z.of_nat (length bs))) as [IN|R]].
+ apply bytes_at_write_other; [apply Z0; lia| lia| lia| cbn [length Z.of_nat]; lia].
+ pose proof (bytes_at_write_same asegs m (A + i) bs ltac:(lia) ltac:(lia)) as BW.
assert (E : exists k', (k' < length bs)%nat /\ k = i + Z.of_nat k') by (exists (Z.to_nat (k - i)); split; lia).
destruct E as (k' & Hk' & ->).
destruct BW as (_ & _ & BW). specialize (BW k' Hk').
pose proof (proj1 (List.Forall_forall _ _) Hbs) as FB.
destruct (nth_error bs k') as [b|] eqn:En; [| apply nth_error_None in En; lia].
assert (b = b8 0) as -> by (apply FB; eapply nth_error_In; exact En).
split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i0 Hi0. cbn [length] in Hi0. assert (i0 = 0%nat) as -> by lia.
cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. replace (A + (i + Z.of_nat k')) with (A + i + Z.of_nat k') by lia. exact BW.
+ apply bytes_at_write_other; [apply Z0; lia| lia| lia| cbn [length Z.of_nat]; lia].
Qed.

Lemma zbytes_write_at : forall m A n a bs,
zbytes m A n -> A <= a -> a + Z.of_nat (length bs) <= A + n -> Forall (fun b => b = b8 0) bs ->
zbytes (write_to_mem m (wa a) bs) A n.
Proof.
intros m A n a bs ZB H1 H2 HF. replace a with (A + (a - A)) by lia. apply zbytes_write; [exact ZB| lia| lia| exact HF].
Qed.

Lemma zbytes_write_other : forall m A n a bs,
zbytes m A n -> 0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> (A + n <= a \/ a + Z.of_nat (length bs) <= A) ->
zbytes (write_to_mem m (wa a) bs) A n.
Proof.
intros m A n a bs [W Z0] H1 H2 HD. split; [apply wr_at_write; exact W|].
intros i Hi. apply bytes_at_write_other; [apply Z0; exact Hi| lia| lia| cbn [length Z.of_nat]; lia].
Qed.

Lemma zbytes_transport : forall W m m' A n,
zbytes m A n -> munch W m m' -> wmono asegs m m' -> disjoint_from W A n -> zbytes m' A n.
Proof.
intros W m m' A n [WR Z0] MU WM HD. split; [eapply wr_at_transport; eauto|].
intros i Hi. eapply bytes_at_transport; [apply Z0; exact Hi| exact MU|].
cbn [length Z.of_nat]. revert HD. clear -Hi. induction W as [|[lo hi] W IH]; cbn; [tauto|]. intros [H1 H2]. split; [lia| apply IH; exact H2].
Qed.

Lemma le8_zero : le8 (wz 0) = repeat (b8 0) 8.
Proof. reflexivity. Qed.

Lemma zbytes_read8 : forall m A n i, zbytes m A n -> 0 <= i -> i + 8 <= n ->
bytes_at asegs m (A + i) (le8 (wz 0)).
Proof.
intros m A n i ZB Hi Hn. pose proof (zbytes_bound _ _ _ ZB) as [B1 B2]. destruct ZB as [_ Z0]. rewrite le8_zero.
assert (GEN : forall k j, 0 <= j -> j + Z.of_nat k <= n -> bytes_at asegs m (A + j) (repeat (b8 0) k)).
{ induction k as [|k IH]; intros j Hj Hk.
- split; [lia|]. split; [cbn; lia|]. intros i0 Hi0; cbn in Hi0; lia.
- cbn [repeat]. change (b8 0 :: repeat (b8 0) k) with ([b8 0] ++ repeat (b8 0) k). apply (proj2 (bytes_at_app _ _ _ _ _)).
split; [apply Z0; lia|]. replace (A + j + Z.of_nat (length [b8 0])) with (A + (j + 1)) by (cbn; lia). apply IH; lia. }
apply GEN; [lia| cbn; lia].
Qed.

Lemma zbytes_load8 : forall m A n a, zbytes m A n -> A <= a -> a + 8 <= A + n ->
ov_read_bytes asegs m (wa a) 8 = Some (le8 (wz 0)).
Proof.
intros m A n a ZB H1 H2.
pose proof (zbytes_read8 m A n (a - A) ZB ltac:(lia) ltac:(lia)) as B. replace (A + (a - A)) with a in B by lia.
pose proof (bytes_at_ov_read asegs m a (le8 (wz 0)) 0%nat 8%nat B ltac:(rewrite length_le8; lia)) as R.
rewrite Z.add_0_r in R. exact R.
Qed.

Lemma zbytes_cells_C8x2 : forall m A n a, zbytes m A n -> A <= a -> a + 16 <= A + n ->
rw_cells asegs m a [C8 (wz 0); C8 (wz 0)].
Proof.
intros m A n a ZB H1 H2. pose proof (zbytes_bound _ _ _ ZB) as [B1 B2].
pose proof (zbytes_read8 m A n (a - A) ZB ltac:(lia) ltac:(lia)) as R1.
pose proof (zbytes_read8 m A n (a + 8 - A) ZB ltac:(lia) ltac:(lia)) as R2.
replace (A + (a - A)) with a in R1 by lia. replace (A + (a + 8 - A)) with (a + 8) in R2 by lia.
destruct ZB as [[_ [_ W]] _].
split; [split; [cbn; auto|]|].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact R1|]. rewrite length_le8. exact R2.
- split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. replace (a + i) with (A + (a - A + i)) by lia. apply W. lia.
Qed.

Lemma Forall_zero_1 : Forall (fun b => b = b8 0) [b8 0].
Proof. repeat constructor. Qed.
Lemma Forall_zero_le8 : Forall (fun b => b = b8 0) (le8 (wz 0)).
Proof. rewrite le8_zero. repeat constructor. Qed.
Lemma Forall_zero_le4 : Forall (fun b => b = b8 0) (le4 (wz 0)).
Proof. change (le4 (wz 0)) with (repeat (b8 0) 4). repeat constructor. Qed.
Ltac is_zero_bytes bs :=
lazymatch bs with
| [Z_to_bv 8 0] => idtac
| le8 (Z_to_bv 64 0) => idtac
| le4 (Z_to_bv 64 0) => idtac
| le1 (Z_to_bv 64 0) => idtac
end.
Ltac zero_bytes_forall :=
first [ exact Forall_zero_1 | exact Forall_zero_le8 | exact Forall_zero_le4
| change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]; exact Forall_zero_1 ].

Ltac transport_chunks_zb segs m a bs :=
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_write_other m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| is_zero_bytes bs; apply (zbytes_write_at m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | zero_bytes_forall ]
| idtac "note: dropping zbytes hypothesis (store inside, not zeros):" H; clear H ]
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_frame segs m A2 xs a bs) in H;
[ | lia | simpl_sizes; slia | simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
end.

Ltac transport_zb_only m a bs :=
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_write_other m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; slia ]
| is_zero_bytes bs; apply (zbytes_write_at m A2 n2 a bs) in H; [ | lia | simpl_sizes; slia | zero_bytes_forall ]
| idtac "note: dropping zbytes hypothesis (store inside, not zeros):" H; clear H ]
end.

Ltac zb_transport m m' MUc WMc :=
let W := lazymatch type of MUc with munch ?W _ _ => W end in
repeat match goal with
| H : zbytes m ?A2 ?n2 |- _ =>
first [ apply (zbytes_transport W m m' A2 n2) in H; [ | exact MUc | exact WMc | cbn [disjoint_from]; slia ]
| idtac "note: dropping zbytes hypothesis (not disjoint from callee footprint):" H; clear H ]
end.

Ltac post_call_zb segs m :=
let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ m ?m' =>
zb_transport m m' MUc WMc;
repeat match goal with
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_chain' _ m m' W m0 MUc) in H; [| sub_fp_solve]
| fail 100 "callee footprint interval not inside the caller footprint (sub_fp_solve)" ]
end;
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (lazymatch goal with
| |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end).

Ltac call_zb SPEC tac :=
lazymatch goal with
| |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
eapply evt_cut;
[ eapply SPEC
| let ms' := fresh "ms'" in let PO := fresh "POST" in
intros ms' PO; hnf in PO; tac PO; revert ms' PO; post_call_zb segs m ]
end.

Ltac call_sp_zb SPEC tac :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call_zb SPEC tac; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call_zb SPEC tac; unname_sp
| _ => call_zb SPEC tac
end.

Ltac zstore ZB SOK :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; zstore ZB SOK
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m (Z_to_bv 64 ?a) ?bs) _) =>
change (write_to_mem m (Z_to_bv 64 a) bs) with (write_to_mem m (wa a) bs);
lazymatch goal with
| MI : mem_inv _ m |- _ => apply (mem_inv_store asegs m (wa a) bs) in MI; [| exact SOK]
end;
clear SOK;
transport_chunks_zb asegs m a bs;
footprint_after_store asegs m a bs;
let m' := fresh "m" in set (m' := write_to_mem m (wa a) bs) in *; clearbody m'; try clear m
end.

Ltac bytes_eq_tac :=
cbn [cells_bytes cbytes app]; rewrite ?le8_lit, ?le4_lit, ?le2_lit, ?le1_lit; cbn [Z_to_le_bytes Z.shiftr Z.shiftl Pos.iter Z.div2];
repeat (first [reflexivity | apply (f_equal2 cons); [apply b8_eqm; vm_compute; reflexivity|]]).

Ltac recast H cs' :=
apply (rw_cells_recast' asegs _ _ _ cs') in H; [| cbn; repeat split; reflexivity | bytes_eq_tac].

Ltac has_var e := match e with context [bv_unsigned _] => idtac end.
Ltac fold_swrap :=
repeat match goal with
| |- context [bv_swrap 32 ?e] =>
first [ has_var e; fail 1
| let v := eval vm_compute in (bv_swrap 32 e) in change (bv_swrap 32 e) with v ]
end.

Ltac at_spin :=
lazymatch goal with |- at_nodeA _ _ NSetTid (MS _ _ (Z_to_bv 64 ?pc) _ None _ _) =>
cbn [at_nodeA]; split; [reflexivity|];
unfold RiscvSemantics.step_accesses; cbn [ms_pc ms_pc_val MS];
match goal with |- context [fetch_word ?s ?p] =>
let w := eval vm_compute in (fetch_word s p) in replace (fetch_word s p) with w by (vm_compute; reflexivity) end;
unfold decode_exec_accesses;
match goal with |- context [is_ecall ?w] =>
let b := eval vm_compute in (is_ecall w) in replace (is_ecall w) with b by (vm_compute; reflexivity) end;
match goal with |- context [decode_any ?w] =>
let d := eval vm_compute in (decode_any w) in replace (decode_any w) with d by (vm_compute; reflexivity) end;
cbn; unfold rset, with_pc; cbn;
replace (Z_to_bv 64 pc + sext 64 0)%bv with (Z_to_bv 64 pc) by (apply bv_eq; vm_compute; reflexivity);
reflexivity
end.

Lemma u64arr_snoc_junk : forall m A ws, u64arr asegs m A ws ->
hjunk m (A + 8 * Z.of_nat (length ws)) (A + 8 * Z.of_nat (length ws) + 8) ->
exists w, u64arr asegs m A (ws ++ [w]).
Proof.
intros m A ws [B W] HJ. destruct (hjunk_C8 m _ HJ) as [w [[_ Bw] Ww]].
cbn [cells_bytes cbytes app cells_size csize Nat.add] in Bw, Ww. rewrite app_nil_r in Bw.
exists w. split.
- rewrite u64s_app. apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact B|]. rewrite u64s_length. cbn [u64s]. rewrite app_nil_r.
replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact Bw.
- destruct W as (W1 & W2 & W). destruct Ww as (V1 & V2 & V). rewrite length_app. cbn [length].
split; [lia|]. split; [lia|]. intros i Hi.
destruct (Z.lt_ge_cases i (8 * Z.of_nat (length ws))); [apply W; lia|].
replace (A + i) with (A + 8 * Z.of_nat (length ws) + (i - 8 * Z.of_nat (length ws))) by lia. apply V. lia.
Qed.

Lemma slot24_geom {BAND : Band} : forall a G RE X m j t, RPrim a G RE X m -> rlay_ok RE X -> tag_at G 24 j = Some t ->
let B := slot_beg RE 24 j in
0 <= j /\ B = reg_beg (ae_L RE) 24 + j * 8192
/\ reg_beg (ae_L RE) 24 <= B /\ B + 8192 <= reg_beg (ae_L RE) 24 + c_alloc_user (cls a 24)
/\ c_alloc_user (cls a 24) <= c_mapped_user (cls a 24) /\ c_mapped_user (cls a 24) <= kFreeArrayOffset
/\ reg_beg (ae_L RE) 24 = prim_lo RE + 24 * 4294967296
/\ KHI <= prim_lo RE /\ prim_hi RE <= band_lo /\ prim_hi RE = prim_lo RE + 137438957568
/\ B mod 16 = 0 /\ prim_lo RE mod 65536 = 0.
Proof.
intros a G RE X m j t RP RL Ht.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & _).
pose proof (HCall 24 ltac:(rewrite K32; lia)) as CR.
pose proof (crep_slot_geom a G RE X m 24 (K 24) j t CR ltac:(lia) Ht) as (I0 & I1 & _ & _ & SB & AU & MU & _).
rewrite class_size_24 in *.
pose proof (reg_geom RE X RL 24 ltac:(lia)) as (RB & _ & PAL & PK & PH & PHE & _).
cbv zeta. rewrite ?KHI_eq. repeat split; try lia.
all: rewrite SB, RB; Z.div_mod_to_equations; lia.
Qed.

Lemma alloc_user_bounds : forall a G RE X m c, RPrim a G RE X m -> 0 <= c < 32 ->
0 <= c_alloc_user (cls a c) /\ c_alloc_user (cls a c) <= c_mapped_user (cls a c) /\ c_mapped_user (cls a c) <= kFreeArrayOffset.
Proof.
intros a G RE X m c RP Hc. destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & _).
destruct (HCall c ltac:(rewrite K32; lia)) as (_ & PU & _).
destruct PU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & G5). lia.
Qed.

Lemma hjunk_C8x4 : forall m a, hjunk m a (a + 32) -> exists w0 w1 w2 w3 : word, rw_cells asegs m a [C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
intros m a HJ. destruct (hjunk_split m a (a + 16) (a + 32) HJ ltac:(lia)) as [H1 H2].
destruct (hjunk_C8x2 m a H1) as (w0 & w1 & C1). replace (a + 32) with (a + 16 + 16) in H2 by lia.
destruct (hjunk_C8x2 m (a + 16) H2) as (w2 & w3 & C2).
exists w0, w1, w2, w3. apply (proj2 (rw_cells_app asegs m a [C8 w0; C8 w1] [C8 w2; C8 w3])). split; [exact C1|]. cbn. exact C2.
Qed.

Lemma rw_cells_C8_u64arr1 : forall m A (w : word), rw_cells asegs m A [C8 w] -> u64arr asegs m A [w].
Proof.
intros m A w [[_ B] W]. cbn [cells_bytes cbytes app cells_size csize Nat.add] in B, W. rewrite app_nil_r in B.
split; [cbn [u64s]; rewrite app_nil_r; exact B| cbn [length Z.of_nat]; exact W].
Qed.

Lemma fp_RPrim_not_Tq {BAND : Band} : forall G RE X x, rlay_ok RE X -> fp_RPrim G RE X x -> ~ (rl_T X + 80 <= x < rl_T X + 208).
Proof.
intros G RE X x RL F. pose proof (rlay_prim_facts RE X RL) as (P0 & P1 & P2 & _).
pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD. cbn [fst snd] in TD.
pose proof kconsts as (KR & KO & KS & K32 & _).
rewrite ?KHI_eq in *. unfold prim_lo, prim_hi, region_info in *.
destruct F as [F|[F|[F|[F|[[F _]|[F _]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. unfold region_info in *. lia.
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. lia.
- destruct F as (c & Hc & F1 & F2). unfold fa_beg, reg_beg in *. rewrite KR, KO, KS, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold fa_beg, reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, KS, K32 in *.
Z.div_mod_to_equations. nia.
- destruct F as (c & Hc & F1 & F2). unfold reg_beg in *. rewrite KR, KO, K32 in *. nia.
- destruct F as (c & Hc & [F1 F2]). cbn [fst snd] in F1, F2. unfold reg_beg, SH, A_SHADOW_OFS in *. rewrite KR, KO, K32 in *.
Z.div_mod_to_equations. nia.
Qed.

Lemma fp_RPrim_not_slot {BAND : Band} : forall a G RE X m c i t x,
RPrim a G RE X m -> rlay_ok RE X -> tag_at G c i = Some t -> tag_prim t = false ->
fp_RPrim G RE X x -> ~ in_iv (slot_beg RE c i, class_size c) x /\ ~ in_sh (slot_beg RE c i, class_size c) x.
Proof.
intros a G RE X m c i t x RP RL Ht Hp F.
destruct (RPrim_open _ _ _ _ _ RP) as (K & _ & GNE & HCall).
pose proof kconsts as (KR & KO & KS & K32 & KP & KU & KM & KX).
pose proof (tag_at_Some_lt G c i t Ht) as [I0 I1].
assert (NE : G c <> []) by (intros E; unfold ncarved in I1; rewrite E in I1; cbn in I1; lia).
pose proof (GNE c NE) as Hc. rewrite K32 in Hc.
pose proof (crep_slot_geom a G RE X m c (K c) i t (HCall c ltac:(rewrite K32; lia)) ltac:(lia) Ht) as (_ & IB & S32 & SM & SB & AU & MU & k & K0 & K1 & K2).
replace ((i + 1) * class_size c) with (i * class_size c + class_size c) in IB by lia. rewrite K1 in IB, SB.
pose proof (reg_geom RE X RL c ltac:(lia)) as (RB & FB & PAL & PK & PH & PHE & RI).
pose proof (class_size_facts c ltac:(lia)) as [CS1 CS2].
rewrite KO in MU. unfold in_iv, in_sh. cbn [fst snd].
assert (SHR : forall z, SH z = z / 8 + 2147450880) by (intros; reflexivity).
assert (HB : reg_beg (ae_L RE) c <= slot_beg RE c i /\ slot_beg RE c i + class_size c <= reg_beg (ae_L RE) c + 3758096384) by lia.
destruct F as [F|[F|[F|[F|[[F NS]|[F NS]]]]]].
- destruct F as [F1 F2]; cbn [fst snd] in F1, F2. rewrite RI in F1, F2. rewrite RB in HB. split; [lia|]. rewrite !SHR. Z.div_mod_to_equations. lia.
- pose proof (rlay_obj_facts RE X _ RL (T_obj RE X)) as (_ & TK & TB & TD & _). cbn [fst snd] in TK, TB, TD. unfold iv_disjoint in TD. cbn [fst snd] in TD.
unfold prim_lo, prim_hi in *. destruct F as [F1 F2]; cbn [fst snd] in F1, F2. rewrite RB in HB. split; [lia|]. rewrite !SHR. rewrite ?KHI_eq in TK. Z.div_mod_to_equations. lia.
- destruct F as (c' & Hc' & F1 & F2). pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & FB' & _). rewrite FB' in F1, F2. rewrite KS in F2.
rewrite RB in HB. split; [lia|]. rewrite !SHR. Z.div_mod_to_equations. lia.
- destruct F as (c' & Hc' & [F1 F2]). cbn [fst snd] in F1, F2. pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & FB' & _). rewrite FB' in F1, F2. rewrite KS in F2.
rewrite RB in HB. rewrite !SHR in *. split; Z.div_mod_to_equations; lia.
- split.
+ intros Hx. apply NS. exists c, i, t. split; [exact Ht|]. split; [rewrite Hp; reflexivity| exact Hx].
+ destruct F as (c' & Hc' & F1 & F2). pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _). rewrite RB' in F1, F2. rewrite KO in F2.
rewrite RB in HB. rewrite !SHR. Z.div_mod_to_equations. lia.
- split.
+ destruct F as (c' & Hc' & [F1 F2]). cbn [fst snd] in F1, F2. pose proof (reg_geom RE X RL c' ltac:(lia)) as (RB' & _). rewrite RB' in F1, F2. rewrite KO in F2.
rewrite RB in HB. rewrite !SHR in *. Z.div_mod_to_equations. lia.
+ intros Hx. apply NS. exists c, i, t. split; [exact Ht|]. split; [rewrite Hp; reflexivity| exact Hx].
Qed.

Lemma batches_mem_nx_keep : forall (P : Z -> Prop) RE m m' QA bs J fin,
batches_mem_nx RE m QA bs J fin -> Forall bwf bs -> agree_on asegs P m m' -> wmono asegs m m' ->
(forall j x, In j J -> in_iv (slot_beg RE 24 j, class_size 24) x \/ in_sh (slot_beg RE 24 j, class_size 24) x -> P x) ->
batches_mem_nx RE m' QA bs J fin.
Proof.
intros P RE m m' QA bs J fin BM FB AG WM HP. eapply batches_mem_nx_agree; [exact AG| exact BM| | | exact FB].
- apply List.Forall_forall. intros j Hj x Hx. apply (HP j x Hj). left; exact Hx.
- apply List.Forall_forall. intros j Hj x Hx. apply (HP j x Hj). right; exact Hx.
Qed.

Lemma upd_snoc {A} : forall (ws : list A) w v, upd (ws ++ [w]) (length ws) v = ws ++ [v].
Proof. induction ws as [|x ws IH]; intros w v; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma fold_right_add_app : forall l1 l2, fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof. induction l1 as [|x l1 IH]; intros l2; cbn; [lia|]. rewrite IH. lia. Qed.

Lemma bwf_snoc : forall b p, bwf b -> b_count b < kBatchCount -> 0 <= aptr_req p <= 2^26 ->
bwf (mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + aptr_used p)).
Proof.
intros b p (B1 & B2 & B3 & B4) HC HP. unfold bwf. cbn [b_chunks b_count b_size].
rewrite length_app, map_app, fold_right_add_app. cbn [length fold_right map]. split; [lia|]. split; [lia|]. split; [lia|].
apply Forall_app. split; [exact B4| constructor; [exact HP| constructor]].
Qed.

Lemma bwf_single : forall p, 0 <= aptr_req p <= 2^26 -> bwf (mkB [p] 1 (aptr_used p + kBatchBytes)).
Proof.
intros p HP. unfold bwf. cbn. pose proof kq_consts as (_ & _ & KC & _). rewrite KC. split; [reflexivity|]. split; [lia|]. split; [lia|].
constructor; [exact HP| constructor].
Qed.

Lemma qwf_append_last : forall front b p qb,
qwf (mkQ (front ++ [b]) qb) -> b_count b < kBatchCount -> 0 <= aptr_req p <= 2^26 ->
qwf (mkQ (front ++ [mkB (b_chunks b ++ [p]) (b_count b + 1) (b_size b + aptr_used p)]) (qb + aptr_used p)).
Proof.
intros front b p qb [HF HB] HC HP. cbn in *. apply Forall_app in HF as [HF1 HF2]. apply Forall_cons_iff in HF2 as [HB2 _].
split.
- apply Forall_app. split; [exact HF1|]. constructor; [apply bwf_snoc; assumption| constructor].
- rewrite map_app, fold_right_add_app in HB. rewrite map_app, fold_right_add_app. cbn [map fold_right b_size q_bytes] in *. lia.
Qed.

Lemma qwf_push_back : forall q b, qwf q -> bwf b -> qwf (q_push_back q b).
Proof.
intros [l qb] b [HF HB] Hb. unfold q_push_back. cbn in *. split.
- apply Forall_app. split; [exact HF| constructor; [exact Hb| constructor]].
- rewrite map_app, fold_right_add_app. cbn. lia.
Qed.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QTVW.Mq7 QNQk.Mq8 QpY2.Mqi QpY2.Mqg.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).

Definition allocate_entry : Z := 0x3f294.

Definition rz_log (n : Z) : Z :=
if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2
else if n <=? 3968 then 3 else if n <=? 16128 then 4
else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.

Lemma rz_log_range : forall n, 0 <= rz_log n <= 7.
Proof. intros n. unfold rz_log. repeat (destruct (_ <=? _)); lia. Qed.

Lemma rz_size_shift : forall n, rz_size n = Z.shiftl 16 (rz_log n).
Proof. intros n. unfold rz_size, rz_log. repeat (destruct (_ <=? _)); reflexivity. Qed.

Lemma land_mask8 x : (0 <= x < 2^64)%Z -> Z.land x 18446744073709551608 = (x - x mod 8)%Z.
Proof.
intros Hx.
assert (E : 18446744073709551608%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
rewrite land_ldiff_distr_r. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
change (2^3)%Z with 8%Z. pose proof (Z.div_mod x 8). lia.
Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).

Definition alloc_frame (fj : list byte) (canfill : word) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 fj; C8 canfill; C8 (wz 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma alloc_pre1 : forall ra sp gp t0 t1 t2 s0 s1 (canfill : word) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 128 ->
0 <= n < 2^64 -> 0 < tr < 2^64 ->
(forall m1 (u0 u1 u2 u3 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word) fj,
munch [(bv_unsigned sp - 128, bv_unsigned sp)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
rw_cells asegs m1 (bv_unsigned sp + -128) (alloc_frame fj canfill s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 8) canfill (wz 49) v1 v2 v3 v4 v5 v6 v7
(wz 8) s3 s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) (wz 1) u4 u5 u6 u7)
F (wz 0x3f32c) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz A_INSTANCE) (wz n) (wz 8) (wz tr) (wz 1) canfill a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz allocate_entry) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn Htr CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold allocate_entry.
carve_frame 128%nat ST.
do 14 step.
do 6 step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
assert (RT0 : RTconst RE X mm) by (eapply RTconst_munch; [exact RT| exact MU| exact WM| constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor]]) end.
step. call0 (asan_inited_spec RE X); [exact RT0| assumption|]. subst.
step. if_lit.
step. call0 (rss_limit_spec RE X); [exact RT0| assumption|]. subst.
step. if_lit.
step. ifz.
stp. step. if_lit.
stp. step. step. if_lit.
stp. stp. step. if_lit.
step. step.
stp. stp. stp.
step. stp. stp. stp.
step.
replace (zxb 3) with (wz 3) by (vm_compute; reflexivity).
stp. stp. stp.
step. step. if_lit.
stp. stp. stp. step. if_lit.
stp. stp.
step. stf.
eapply CONT; [exact MU| exact WM| assumption| exact ST| exact FR].
Qed.

Lemma alloc_rzlog : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n : Z) (Q : machine_state -> Prop),
0 <= n < 2^62 ->
(forall a0', evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (wz (rz_log n)) s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f400) fc None m (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x3f32c) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros Hn CONT. unfold rz_log in CONT.
step. destruct (Z.leb_spec n 48) as [C0|C0]; ifz.
{ stp. step. apply CONT. }
stp. step. destruct (Z.leb_spec n 96) as [C1|C1]; ifz.
{ stp. step. apply CONT. }
stp. step. destruct (Z.leb_spec n 448) as [C2|C2]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 3968) as [C3|C3]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 16128) as [C4|C4]; ifz.
{ stp. step. apply CONT. }
stp. stp. step. destruct (Z.leb_spec n 32256) as [C5|C5]; ifz.
{ stp. step. apply CONT. }
stp. stp. step.
rewrite v_sltu_b2z. rewrite (unsigned_lit n) by lia. fold_closed_in_goal.
step.
destruct (Z.leb_spec n 64512) as [C6|C6].
- replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. lits. apply CONT.
- replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. lits. apply CONT.
Qed.

Lemma alloc_pre3 : forall ra (sp : word) gp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s8 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (n tr lo : Z) (Q : machine_state -> Prop),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -128) -> band_lo <= lo -> lo <= bv_unsigned sp - 144 ->
0 <= n -> from_primary n = true ->
(forall m1 (u0 u1 u2 u3 v0 v1 v2 v3 v4 v5 v6 v7 u4 u5 u6 u7 : word),
munch [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -128) ->
evt asegs Q (MS (mkR u0 (wz (bv_unsigned sp + -128)) gp (wz A_TP) u1 u2 u3 (wz 1) (wz (used_size n)) v0 v1 v2 v3 v4 v5 v6 v7
(wz 8) (wz (needed n)) (wz (rz_size n)) (wz n) (wz A_INSTANCE) (wz tr) (wz (-8)) (wz 7) (wz (A_INSTANCE + 2047)) s11 u4 u5 u6 u7)
F (wz 0x3f514) fc None m1 (seg_rom asegs))) ->
evt asegs Q (MS (mkR ra (wz (bv_unsigned sp + -128)) gp (wz A_TP) t0 t1 t2 (wz 8) s1 a0 a1 a2 a3 a4 a5 a6 a7
(wz 8) (wz (rz_log n)) s4 (wz n) (wz A_INSTANCE) (wz tr) s8 (wz 7) (wz (A_INSTANCE + 2047)) s11 t3 t4 t5 t6)
F (wz 0x3f400) fc None m (seg_rom asegs)).
Proof.
intros until Q; intros RT RL MI ST CEIL LO Hn HP CONT.
pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
apply from_primary_iff in HP. unfold kMaxSize in HP.
pose proof (needed_facts n Hn) as NF. pose proof (rz_size_range n) as [RZ1 RZ2]. pose proof (rz_log_range n) as RL8.
pose proof (rz_size_shift n) as RZS.
assert (N16 : n <= 65536) by (unfold needed in HP; pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)); lia).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp + -128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 27%nat K27. unfold A_INSTANCE in *.
step.
replace (sx16 (wz 16)) with (wz 16) by (rewrite sx16_any; reflexivity).
step. stp. stp. stp.
step. call_sp (rz_size2log_spec 16); [left; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].
step.
step.
replace (sx16 (wz 2048)) with (wz 2048) by (rewrite sx16_any; reflexivity).
step. stp.
step. call_sp (rz_size2log_spec 2048); [right; reflexivity| assumption| exact ST| exact CEIL'| lia|].
subst. try clear ST. match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
cbn [rz_log_of Z.eqb Pos.eqb].

lazymatch goal with |- evt _ ?Q (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists (v1 : word),
ms1 = MS (@bvmap_set 5 word 10 (wz (Z.max n 8)) (@bvmap_set 5 word 11 v1 (@bvmap_set 5 word 19 (wz (rz_log n)) R))) FF (wz 0x3f448) fcc rv mm ro))
end.
{ step.
assert (NB : rz_log n <> 0 -> 48 < n) by (unfold rz_log; destruct (Z.leb_spec n 48); [intros HH; exfalso; apply HH; reflexivity| lia]).
destruct (Z.eq_dec (rz_log n) 0) as [R0|RP]; ifz.
- step. step. if_lit.
stp. step. step.
destruct (Z.ltb_spec 8 n) as [L8|G8]; ifz.
+ replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R0. reflexivity.
+ stp. replace (Z.max n 8) with 8 by lia. apply evt_done. eexists. simp_regs. rewrite ?R0. reflexivity.
- specialize (NB RP).
step.
destruct (Z.eq_dec (rz_log n) 7) as [R7|R6]; ifz.
+ step.
stp. step. step. ifz.
step.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. rewrite ?R7. reflexivity.
+ stp. step. step. ifz.
replace (Z.max n 8) with n by lia. apply evt_done. eexists. simp_regs. reflexivity. }
intros ms1 [v1 ->]. simp_regs.
set (mx := Z.max n 8) in *. assert (MX : 8 <= mx <= 65536) by lia.
step. stp. stp.
stp. stp.
step.
rewrite (unsigned_lit (mx + 7)), land_mask8 by lia.
assert (RU : mx + 7 - (mx + 7) mod 8 = round_up mx 8) by (unfold round_up; Z.div_mod_to_equations; lia).
rewrite RU. pose proof (round_up_8 mx ltac:(lia)) as [RU1 RU2].
stp. step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia. replace (round_up mx 8 + 0) with (round_up mx 8) by lia.
step.
rewrite ?(unsigned_lit (round_up mx 8)) by lia.
replace (Z.land (round_up mx 8) 7) with 0 by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; lia).
step. if_lit.
assert (NE : needed n = round_up mx 8 + rz_size n) by (unfold needed; reflexivity).
stp. step. stp.
step.
replace (wz (bv_swrap 32 (Z.shiftl 16 (bv_unsigned (wz (rz_log n)) mod 32)))) with (wz (rz_size n)).
2:{ rewrite (unsigned_lit (rz_log n)), Z.mod_small, <- RZS by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31). Z.div_mod_to_equations. lia. }
replace (v_sltiu (wz n) 1) with (wz (if n =? 0 then 1 else 0))
by (unfold v_sltiu; rewrite (unsigned_lit n) by lia; change (bv_wrap 64 1) with 1; destruct (Z.eqb_spec n 0), (Z.ltb_spec n 1); try reflexivity; lia).
stp.
step.
replace (n + (if n =? 0 then 1 else 0)) with (used_size n) by (unfold used_size; destruct (Z.eqb_spec n 0); lia).
step.
step.
rewrite <- NE.
step.
try (match goal with |- context [alu64 ALU_SLTU ?x ?y] => change (alu64 ALU_SLTU x y) with (v_sltu x y) end).
rewrite !v_sltu_b2z. rewrite (unsigned_lit (needed n)) by lia. fold_lit_ux.
replace (needed n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].
stp. stp. stp. stp.
step.
rewrite Z.land_0_l. replace (0 + needed n) with (needed n) by lia.
assert (US : 1 <= used_size n <= 65537) by (unfold used_size; lia).
step. ifz.
step. ifz.
step.
step. ifz.
eapply CONT; [exact MU| exact WM| assumption| exact ST].
Qed.
End S.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsJM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig QwAs.Mq2.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QNQk.Mq6 QXcn QsJM QTVW.Mqa QpY2.Mqh QpY2.Mqf.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition amemset_entry : Z := 0x61fb8.
Definition amemset_frame : Z := 2128.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition amemset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(dst c n lo : Z) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz dst) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ munch [(dst, dst + n); (lo, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' dst [CB (Z.to_nat n) (repeat (b8 c) (Z.to_nat n))].

Lemma u_nm65 : forall n, 1 <= n <= 64 -> bv_unsigned (wz (n + -65)) = 18446744073709551551 + n.
Proof. intros n Hn. rewrite unsigned_lit_wrap. Z.div_mod_to_equations. lia. Qed.

Lemma rw_cells_below : forall m m' A cs W, rw_cells asegs m A cs -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => A + Z.of_nat (cells_size cs) <= fst iv) W -> rw_cells asegs m' A cs.
Proof.
intros m m' A cs W RC MU WM HW.
eapply (rw_cells_agree asegs (fun a => A <= a < A + Z.of_nat (cells_size cs))); [eapply agree_on_of_munch; [exact MU| exact WM|]| exact RC| intros a Ha; exact Ha].
intros x Hx _. clear MU. induction HW as [|[lo hi] W H HW IH]; cbn; [exact I|]. cbn in H. split; [lia| exact IH].
Qed.

Lemma shadow_ok_zrd_head : forall m dst n, shadow_ok m dst n -> 0 < n -> zrd m (SH dst) (SH (dst + n - 1) - SH dst).
Proof.
intros m dst n SO N0 i Hi. rewrite !SH_eq in Hi.
destruct (SO i ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (v & B & C).
assert (v = 0) as -> by (Z.div_mod_to_equations; lia).
match type of B with bytes_at _ _ ?a _ => replace (SH dst + i) with a; [exact B|] end.
rewrite !SH_eq. Z.div_mod_to_equations. lia.
Qed.

Lemma qslow_loop : forall k (p : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (A e : Z) P,
zrd m A (e - A) -> 0 <= A -> A <= p -> p < e -> e <= KHI -> k = Z.to_nat (e - p) ->
(forall a6', evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz e) (wz e) (wz 0) a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62184) fc None m (seg_rom asegs))) ->
evt asegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (wz p) (wz e) (wz 0) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x62174) fc None m (seg_rom asegs)).
Proof.
induction k as [k IH] using lt_wf_ind.
intros until P; intros ZR A0 C1 C2 EK HK K. rewrite ?KHI_eq in EK.
pose proof (zrd_ro1 m A (e - A) p ZR ltac:(lia) ltac:(lia)) as B.
step. stp. stp. step. destruct (Z_lt_le_dec (p + 1) e) as [X1|X1].
- ifz. eapply (IH (Z.to_nat (e - (p + 1)))); [lia| exact ZR| lia| lia| lia| rewrite ?KHI_eq; lia| lia| exact K].
- ifz. replace (p + 1) with e by lia. apply K.
Qed.

Lemma slow_flag_zero : forall r v, 0 <= v < 8 -> 0 <= r < 8 -> (v = 0 \/ r < v) ->
Z.land (bv_unsigned (v_sltu (wz 0) (wz v))) (bv_unsigned (wz (Z.lxor (bv_unsigned (v_slt (wz r) (wz v))) 1))) = 0.
Proof.
intros r v Hv Hr C. unfold v_sltu, c_ltu, bv_ltu, v_slt, c_lts, bv_lts.
rewrite !signed_small, !unsigned_lit by lia. change (bv_unsigned (wz 0)) with 0.
destruct (Z.ltb_spec0 0 v); destruct (Z.ltb_spec0 r v); cbn -[Z.land]; try reflexivity; try lia.
Qed.

Ltac amemset_finish FR ST usp c :=
do 9 step; release_frame FR ST usp; step;
apply evt_done; unfold amemset_post; do 15 eexists; split; [reflexivity|];
lazymatch goal with MU : munch _ _ ?mc |- _ => split; [exact MU|] end;
lazymatch goal with WM : wmono _ _ ?mc |- _ => split; [exact WM|] end;
split; [assumption|]; split; [exact ST|];
lazymatch goal with H : rw_cells _ _ _ [CB _ (repeat _ _)] |- _ => rewrite (Z.mod_small c 256) in H by lia; exact H end.

Lemma amemset_core : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (dst c n lo : Z) (old : list byte) (w1 w2 : word),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 4096 ->
0 <= c < 256 -> 0 < n <= 2^43 -> appr dst n -> dst + n <= band_lo ->
rw_cells asegs m dst [CB (Z.to_nat n) old] ->
shadow_ok m dst n ->
(n <= 64 -> rw_cells asegs m (8 * (SH dst / 8)) [C8 w1] /\ rw_cells asegs m (8 * (SH (dst + n - 1) / 8)) [C8 w2]) ->
evt asegs (amemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc dst c n lo m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz dst) (wz c) (wz n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz amemset_entry) fc None m (seg_rom asegs)).
Proof.
intros until w2; intros RT RL MI ST CEIL LO HC [N0 N43] K1d K2d RC SO NB.
pose proof CEIL as CEIL'. idtac. pose proof K2d as K2d'.
apply appr_to_lia in K1d; [| lia| lia].
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (munch_refl [(dst, dst + n); (lo, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs. pose proof (wmono_refl asegs m) as WM.
unfold amemset_entry.
carve_frame 2128%nat ST.
do 10 istep.

rt_now RT RL 42%nat K42. rt_now RT RL 40%nat K40.
step. stp. stp. step. ifz. clear K42 K40.

stp. step. step. step.
rewrite (unsigned_lit dst), zb_lxor_ones by lia. ifz.

stp. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (SO' : shadow_ok mc dst n)
by (eapply shadow_ok_munch; [exact SO| exact MUs| exact WM| | lia]; intros y Hy; cbn; rewrite !SH_eq in Hy; Z.div_mod_to_equations; lia) end.
destruct (Z_le_gt_dec n 64) as [N64|N65].
-
unfold_cond. fold_lit_ux. rewrite u_nm65 by lia. if_lit.
destruct (NB N64) as [W1 W2].
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W1; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]];
apply (fun H => rw_cells_below m mc _ _ _ H MUs WM) in W2; [| constructor; [cbn; rewrite SH_eq; Z.div_mod_to_equations; lia| constructor]] end.
rt_now RT RL 19%nat K19. rt_now RT RL 5%nat K5.
step. stp. step. stp. stp. step. stp. stp. stp.
rewrite (unsigned_lit dst), (unsigned_lit (dst + n + -1)) by lia.
replace (2147450880 + dst ≫ 3) with (SH dst) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; lia).
replace (2147450880 + (dst + n + -1) ≫ 3) with (SH (dst + n - 1)) by (rewrite Z.shiftr_div_pow2, SH_eq by lia; Z.div_mod_to_equations; lia).
assert (SHR : 0x7fff8000 <= SH dst /\ SH dst <= SH (dst + n - 1) < 0x10007fff8000) by (rewrite !SH_eq; Z.div_mod_to_equations; lia).
stp. stp. rewrite (unsigned_lit (SH dst)), (unsigned_lit (SH (dst + n - 1))) by lia. rewrite !land_m8 by lia.
replace (SH dst - SH dst mod 8) with (8 * (SH dst / 8)) by (Z.div_mod_to_equations; lia).
replace (SH (dst + n - 1) - SH (dst + n - 1) mod 8) with (8 * (SH (dst + n - 1) / 8)) by (Z.div_mod_to_equations; lia).
step. step. stp.

destruct (shadow_ok_last _ dst n SO' ltac:(lia)) as (v1 & B1 & R1 & C1).
pose proof (shadow_ok_zrd_head _ dst n SO' ltac:(lia)) as ZH.
lazymatch goal with |- evt _ _ (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
apply (evt_cut asegs (fun ms1 => exists a3' a5' a6' a7' : word,
ms1 = MS (@bvmap_set 5 word 13 a3' (@bvmap_set 5 word 15 a5' (@bvmap_set 5 word 16 a6' (@bvmap_set 5 word 17 a7' R)))) FF (wz 0x62048) fcc rv mm ro))
end.
{ step. if_cases Hq.
-
step. rewrite (sxb_b8 v1) by lia. stp. rewrite (unsigned_lit (dst + n + -1)), land7 by lia.
step. step. step. step.
match goal with |- context [wz (Z.land ?a ?b)] => replace (Z.land a b) with 0 by (symmetry; apply slow_flag_zero; lia) end.
step. destruct (Z_le_gt_dec (SH (dst + n - 1)) (SH dst)) as [X1|X1].
+ ifz. replace (SH dst) with (SH (dst + n - 1)) by lia. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
+ ifz. eapply (qslow_loop (Z.to_nat (SH (dst + n - 1) - SH dst)) (SH dst)); [exact ZH| lia| lia| lia| rewrite ?KHI_eq; lia| reflexivity|].
intros a6'. stp. step. ifz. apply evt_done. do 4 eexists. simp_regs. reflexivity.
- apply evt_done. do 4 eexists. simp_regs. reflexivity. }
intros ms1 (a3' & a5' & a6' & a7' & ->). simp_regs.

rt_now RT RL 23%nat K23. step. stp. step. clear K23 K19 K5.
clear MUs. call_u memset_spec. { rewrite ?unsigned_lit by lia. exact RC. } { assumption. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
amemset_finish FR ST' (bv_unsigned sp) c.
-
ifz. step. ifz.
step. step. step. step. step.
call_u rip_spec_lh; [rt_solve RT RL| exact RL| assumption| unsigned_lits; exact ST| exact CEIL'| unsigned_lits; lia| exact SO'| lia| rewrite ?KHI_eq; lia|].
match goal with H : RTconst RE X ?mc |- evt _ _ (MS _ _ _ _ _ ?mc' _) => constr_eq mc mc'; rename H into RT1 end.
step. step. step. step. step. ifz.

rtc RT1 23%nat K23. step. stp. step. clear K23.
clear MUs. call_u memset_spec. { rewrite ?unsigned_lit by lia. exact RC. } { assumption. }
match goal with H : stk asegs _ lo _ |- _ => rename H into ST' end.
amemset_finish FR ST' (bv_unsigned sp) c.
Qed.

End S.

Section Lift.
Context {BAND : Band}.
Variable C : arun_components.
Hypothesis HRT : forall RE X m, ac_RTconst C RE X m <-> RTconst RE X m.
Hypothesis HRP : forall a G RE X m, ac_RPrim C a G RE X m <-> RPrim a G RE X m.
Hypothesis HRC : forall a LB G RE X m, ac_RChunks C a LB G RE X m <-> RChunks a LB G RE X m.
Hypothesis HRQ : forall a LB G RE X m, ac_RQuar C a LB G RE X m <-> RQuar a LB G RE X m.
Hypothesis HRF : forall FS RE X m, ac_RFake C FS RE X m <-> RFake FS RE X m.

Lemma asan_memset_A : aasan_memsetA_stmt asegs a_alayout (ARUN C).
Proof.
unfold aasan_memsetA_stmt. intros until lo; intros old s LB FS RE AR ST CEIL LO MI Ha0 Ha1 Ha2 HC HN RC SB SHD K1 K2 WH.
destruct (ARUN_open C _ _ _ _ _ AR) as (X & G & LB0 & FS0 & PB & PF & AX).
pose proof AX as (GC & R1 & _ & R3 & R4 & _ & R6 & _ & R8).
pose proof (proj1 GC) as RL.
apply HRT in R1. apply HRP in R3. apply HRC in R4. apply HRQ in R6. apply HRF in R8.
subst a0 a1 a2. cbn [ala_asan_memset ala_memset_stack a_alayout] in *.

assert (WH0 : 64 < n <= 2^43 \/ amemset_whereA LB0 FS0 dst n).
{ destruct WH as [W|[(p & A & n0 & Hin & W)|(cl & f & Hin & W)]]; [left; exact W| right; left| right; right].
- exists p, A, n0. split; [eapply Permutation_in; [exact PB| exact Hin]| exact W].
- exists cl, f. split; [eapply Permutation_in; [exact PF| exact Hin]| exact W]. }
assert (N43 : 0 < n <= 2^43).
{ destruct WH0 as [W|[(p & A & n0 & Hin & W)|(cl & f & Hin & W)]]; [lia| |].
- pose proof (gc_block_small _ _ _ _ _ _ GC p A n0 Hin). lia.
- destruct R8 as (_ & _ & _ & [SHf _] & _). destruct (SHf _ Hin) as (Hc & _). cbn [ff_cls fst] in Hc. unfold kFsClasses in Hc.
unfold ff_size in W. assert (2 ^ cl <= 2 ^ 10) by (apply Z.pow_le_mono_r; lia). lia. }
assert (NB : exists w1 w2 : word, n <= 64 ->
rw_cells asegs m (8 * (SH dst / 8)) [C8 w1] /\ rw_cells asegs m (8 * (SH (dst + n - 1) / 8)) [C8 w2]).
{ destruct (Z_le_gt_dec n 64) as [LE|GT].
- destruct WH0 as [W|W]; [lia|].
destruct (amemset_nbhd _ LB0 FS0 G RE X m GC R3 R4 R6 R8 dst n W ltac:(lia)) as [J1 J2].
destruct (hjunk_C8 m _ J1) as [w1 Hw1]. destruct (hjunk_C8 m _ J2) as [w2 Hw2].
exists w1, w2. intros _. split; [exact Hw1| exact Hw2].
- exists (wz 0), (wz 0). intros LE. lia. }
destruct NB as (w1 & w2 & NB).
eapply (amemset_core RE X); try eassumption; try lia.
Qed.
End Lift.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig.
Import Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QUvT.Mq0 QbcP_c1 QWRO QFQR QmP7 QKBN QN4c QNQk.Mq8 QNQk QsJM QpY2 QpY2.Mqe.
Import QlES. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).

Definition fsmalloc0_entry : Z := 0x4a9bc.
Definition fsmalloc9_entry : Z := 0x4ab30.
Definition fsmalloc_stack : Z := 48 + tls_fs_stack.

Section Walk.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).
Local Notation FS := (ae_fs_base RE).

Lemma filter_cls_length : forall c FS0,
length (filter (fun f : fframe => ff_cls f =? c) FS0) = length (List.filter (fun f => ff_cls f =? c) FS0).
Proof.
intros c FS0. induction FS0 as [|f l IH]; [reflexivity|]. rewrite filter_cons. cbn [List.filter].
destruct (decide _) as [D|D]; destruct (ff_cls f =? c) eqn:E.
- cbn [length]. rewrite IH. reflexivity.
- exfalso. exact D.
- exfalso. apply D. exact I.
- exact IH.
Qed.

Lemma land_16383 : forall x, Z.land x 16383 = x mod 16384.
Proof. intros x. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma mod16384_of_64 : forall x, (x mod 2^64) mod 16384 = x mod 16384.
Proof. intros x. apply Z.mod_mod_divide. exists (2^50); reflexivity. Qed.

Lemma fs0_scan : forall mc fl FS0 (u : Z) (k : nat) (i : Z) (cur : word)
(ra sp gp tp t0 t1 t2 s0 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc,
u8arr asegs mc (FS + 4096) fl -> fl = flags_of FS0 FS 0 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 0) FS0)) < fs_N 0 ->
0 <= FS -> FS + 11571200 <= 2^64 ->
k = Z.to_nat (16384 - i) -> 0 <= i < 16384 ->
bv_unsigned cur mod 16384 = (u + i) mod 16384 ->
(forall j, 0 <= j < i -> live_b FS0 0 (fs_frame FS 0 ((u + j) mod 16384)) = true) ->
evt asegs (fun ms' => exists (pos i' : Z) (cur' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (16384 - i')) (wz (FS + 4096)) cur' (wz 16383) a4
(wz (FS + 4096 + pos)) (wz pos) (wz 0) (wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4aab8) fc None mc (seg_rom asegs)
/\ 0 <= pos < 16384 /\ live_b FS0 0 (fs_frame FS 0 pos) = false /\ 0 <= i' < 16384)
(MS (mkR ra sp gp tp t0 t1 t2 s0 (wz FS) (wz (16384 - i)) (wz (FS + 4096)) cur (wz 16383) a4 a5 a6 a7
(wz 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz 0x4aa40) fc None mc (seg_rom asegs)).
Proof.
intros mc fl FS0 u k. induction k as [k IH] using lt_wf_ind.
intros i cur; intros until fc; intros FLc Efl ROOM B1 B2 Hk Hi Hcur BUSY.
pose proof (bv_unsigned_in_range 64 cur) as CR. change (bv_modulus 64) with (2^64) in CR.
set (pos := Z.land (bv_unsigned cur) 16383).
assert (Hpos : pos = (u + i) mod 16384) by (subst pos; rewrite land_16383; exact Hcur).
assert (PR : 0 <= pos < 16384) by (rewrite Hpos; apply Z.mod_pos_bound; lia).
destruct (live_b FS0 0 (fs_frame FS 0 pos)) eqn:LB.
-
pose proof (u8arr_read asegs mc (FS + 4096) fl pos (b8 1) (wa (FS + 4096 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_false. istep. rewrite addiw_small by lia. do 2 istep.
destruct (Z.lt_ge_cases (i + 1) 16384) as [LT|GE].
+ if_true_u. replace (16384 - i + -1) with (16384 - (i + 1)) by lia.
eapply (IH (Z.to_nat (16384 - (i + 1))) ltac:(lia) (i + 1) (wz (bv_unsigned cur + 1)));
[exact FLc| exact Efl| exact ROOM| lia| lia| reflexivity| lia| |].
* rewrite unsigned_lit_wrap, mod16384_of_64, <- Zplus_mod_idemp_l, Hcur, Zplus_mod_idemp_l. f_equal. lia.
* intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia].
+ exfalso.
assert (ALL : forall p, 0 <= p < fs_N 0 -> live_b FS0 0 (fs_frame FS 0 p) = true).
{ apply (scan_exhausts FS0 FS 0 u (i + 1)); try change (fs_N 0) with 16384; [lia| lia| lia| | lia].
intros j Hj. destruct (Z.eq_dec j i) as [->|NE]; [rewrite <- Hpos; exact LB| apply BUSY; lia]. }
pose proof (all_live_count FS0 FS 0 ltac:(lia) ALL) as CNT. change (fs_N 0) with 16384 in CNT, ROOM.
rewrite filter_cls_length in ROOM. lia.
-
pose proof (u8arr_read asegs mc (FS + 4096) fl pos (b8 0) (wa (FS + 4096 + pos)) FLc
ltac:(subst fl; rewrite flags_of_nth by (unfold fs_N; cbn; lia); rewrite LB; reflexivity) ltac:(lia) eq_refl) as RD.
subst pos. do 4 istep. if_true. apply evt_done. exists (Z.land (bv_unsigned cur) 16383), i, cur.
split; [reflexivity|]. split; [exact PR|]. split; [exact LB| exact Hi].
Qed.

Lemma fsmalloc0_spec : forall ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m lo FS0 (size : Z),
RTconst RE X m -> rlay_ok RE X -> RFake FS0 RE X m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - 224 ->
Z.of_nat (length (filter (fun f => ff_cls f =? 0) FS0)) < fs_N 0 ->
a0 = wz size ->
evt asegs (rpost ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
[(FS, FS + A_FS_MAP_SIZE); (SH FS, SH (FS + A_FS_MAP_SIZE)); (bv_unsigned sp - 224, bv_unsigned sp)] lo m
(fun a0' m' => exists f pos junk,
a0' = wz f /\ f = fs_frame FS 0 pos /\ 0 <= pos < fs_N 0 /\ ~ In f (map ff_addr FS0)
/\ fframe_rangeA RE 0 f
/\ RTconst RE X m' /\ RFake ((0, f) :: FS0) RE X m'
/\ rw_cells asegs m' f [CB (Z.to_nat (ff_size 0 - 8)) junk]
/\ rw_cells asegs m' (SH f) [C8 (wz 0)]
/\ munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS, FS + 8); (fs_flag FS 0 pos, fs_flag FS 0 pos + 1);
(f, f + ff_size 0); (SH f, SH f + ff_size 0 / 8)] m m'))
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz fsmalloc0_entry) fc None m (seg_rom asegs)).
Proof.
intros until size; intros RT RL RF MI ST CEIL LO ROOM Ha0. pose proof CEIL as CEIL'. idtac.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
unfold fsmalloc0_entry, fsmalloc_stack, tls_fs_stack, A_TP, A_FS_MAP_SIZE in *. subst a0.
obj_facts RL.

pose proof RF as RF0.
destruct RF as (ALf & K1f & K2f & SHP & SSL & GC & HI & FL & SL & J1 & J2).
destruct (HI 0 ltac:(unfold kFsClasses; lia)) as [h0 HINT]. unfold fs_hint in HINT. rewrite Z.mul_0_r, Z.add_0_r in HINT.
pose proof (FL 0 ltac:(unfold kFsClasses; lia)) as FL0.
remember (flags_of FS0 FS 0) as fl eqn:Efl.
assert (LENF : Z.of_nat (length fl) = 16384) by (subst fl; rewrite flags_of_length; reflexivity).
replace (fs_flag FS 0 0) with (FS + 4096) in FL0 by (unfold fs_flag, fs_foff; cbn; lia).
pose proof (munch_refl [(FS, FS + 11571200); (SH FS, SH (FS + 11571200)); (bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MUs.
pose proof (wmono_refl asegs m) as WM.
carve_frame 32%nat ST.
step_until 0x55798.

call_u (tls_fs_spec RE X).
{ rt_cur RT RL RTn. exact RTn. } { exact RL. } { assumption. } { unsigned_lits. exact ST. } { exact CEIL'. } { unsigned_lits. lia. }
unfold A_TP in *.

rt_now RT RL 30%nat K30. step_until 0. clear K30. if_false_u.

step_until 0. if_true_u.

step_until 0. if_false. step_until 0x4aa40.

eapply evt_cut.
{ eapply (fs0_scan _ fl FS0 (bv_unsigned h0) _ 0 h0);
[exact FL0| exact Efl| exact ROOM| lia| lia| reflexivity| lia| f_equal; lia| intros j Hj; lia]. }
cbv beta. intros ms' (pos & i' & cur' & -> & PR & LB & Hi').
match goal with H : stk asegs _ lo _ |- _ => rename H into STK end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eassert (MU2 : munch [(bv_unsigned sp - 224, bv_unsigned sp); (FS, FS + 8); (FS + 4096 + pos, FS + 4096 + pos + 1);
(FS + 36864 + pos * 64, FS + 36864 + pos * 64 + 64); (SH (FS + 36864 + pos * 64), SH (FS + 36864 + pos * 64) + 8)] m mc)
by (eapply munch_weaken; [| exact MUs]; intros y Hy; cbn [outside fst snd] in Hy |- *; tauto) end.
clear MUs.

do 4 istep. rewrite (unsigned_lit pos), Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
istep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
pose proof (u8arr_store_ok asegs mc (FS + 4096) fl pos (wa (FS + 4096 + pos)) FL0 ltac:(lia) eq_refl) as SOK end.
step. rewrite le1_lit.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mc _ _) _) =>
pose proof (u8arr_write asegs mc (FS + 4096) fl pos (b8 1) FL0 ltac:(lia)) as FL1 end.
clear FL0. store_done.

do 3 istep.
remember (FS + 36864 + pos * 64) as f eqn:Ef in *.
assert (FB : FS + 36864 <= f /\ f + 64 <= FS + 36864 + 1048576) by (subst f; lia).
pose proof (hjunk_wmono _ _ _ _ J1 WM) as J1c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J1c.
pose proof (fun Hm => proj2 (hjunk_split _ _ f _ J1c Hm)) as J1r. specialize (J1r ltac:(lia)).
pose proof (fun Hm => proj1 (hjunk_split _ f (f + Z.of_nat 64) _ J1r Hm)) as J1f. specialize (J1f ltac:(cbn; lia)).
destruct (hjunk_cells _ f 64 J1f) as [junkf FRM]. clear J1c J1r J1f.
do 2 istep.

do 2 istep. call0 (mem_to_shadow_spec RE X).
{ rt_solve RT RL. } { assumption. } { rewrite ?KHI_eq. lia. }
match goal with H : @eq (bv 64) ?v (wz (SH f)) |- _ => subst v end.
do 3 istep.

assert (SHf8 : SH (f + 64) = SH f + 8) by (rewrite !SH_eq; replace (f + 64) with (f + 8 * 8) by lia; rewrite Z.div_add by lia; lia).
assert (SHK : 0x7fff8000 <= SH FS /\ SH (FS + 11571200) <= 0x10007fff8000)
by (clear - OF; rewrite !SH_eq; Z.div_mod_to_equations; lia).
assert (SB : SH FS <= SH f /\ SH (f + 64) <= SH (FS + 11571200)) by (split; apply SH_mono; lia).
pose proof (hjunk_wmono _ _ _ _ J2 WM) as J2c. unfold fs_area_lo, fs_area_hi, A_FS_MAP_SIZE in J2c.
pose proof (fun Hm => proj2 (hjunk_split _ _ (SH f) _ J2c Hm)) as J2r. specialize (J2r ltac:(split; apply SH_mono; lia)).
pose proof (fun Hm => proj1 (hjunk_split _ (SH f) (SH f + Z.of_nat 8) _ J2r Hm)) as J2f. specialize (J2f ltac:(cbn; lia)).
destruct (hjunk_cells _ (SH f) 8 J2f) as [junks SHC]. clear J2c J2r J2f.
istep.

step_until 0.
release_frame FR STK (bv_unsigned sp).
apply evt_done. unfold rpost. do 16 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact STK|].

pose proof (rw_cells_merge asegs _ f [] [CB 24 (take 24 junkf); C8 sp; CB 24 (take 24 (drop 32 junkf))] [C8 (wz (FS + 4096 + pos))] FRM) as FRM'.
cbn [app cells_size csize cells_bytes cbytes Nat.add] in FRM'.
rewrite app_nil_r in FRM'.
destruct (proj1 (rw_cells_app asegs _ f [CB 56 (take 24 junkf ++ le8 sp ++ take 24 (drop 32 junkf))] [C8 (wz (FS + 4096 + pos))]) FRM') as [BODY SLOT].
cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SLOT. clear FRM FRM'.
assert (Ef' : f = fs_frame FS 0 pos) by (subst f; unfold fs_frame, ff_size; cbn; lia).
assert (FLG : fs_flag FS 0 pos = FS + 4096 + pos) by (unfold fs_flag, fs_foff; cbn; lia).
assert (FLG0 : fs_flag FS 0 0 = FS + 4096) by (unfold fs_flag, fs_foff; cbn; lia).
edestruct (RFake_take RE X FS0 m _ 0 pos f (wz (bv_unsigned cur' + 1)) RF0 ltac:(unfold kFsClasses; lia) ltac:(change (fs_N 0) with 16384; lia) Ef'
ltac:(rewrite Ef'; exact LB) WM) as [RF' FRESH].
{ eapply agree_on_of_munch; [exact MU2| exact WM|]. intros y [Fy NT] Hy. apply outside_intro. intros lo' hi' Hin [Y1 Y2].
apply (fp_RFake_zone RE X) in Fy. unfold in_iv, in_sh, A_FS_MAP_SIZE in Fy. cbn [fst snd] in Fy.
unfold fs_touched, fs_hint in NT. rewrite FLG in NT. change (ff_size 0) with 64 in NT. change (64 / 8) with 8 in NT.
change (11571200 / 8) with 1446400 in Fy. cbn in Hin.
assert (SHD : SH (FS + 11571200) = SH FS + 1446400)
by (rewrite !SH_eq; replace (FS + 11571200) with (FS + 1446400 * 8) by lia; rewrite Z.div_add by lia; lia).
destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-; lia. }
{ unfold fs_hint. rewrite Z.mul_0_r, Z.add_0_r. exact HINT. }
{ rewrite FLG0, <- Efl. exact FL1. }
{ replace (f + ff_size 0 - 8) with (f + 56) by (change (ff_size 0) with 64; lia). rewrite FLG. exact SLOT. }
exists f, pos, (take 24 junkf ++ le8 sp ++ take 24 (drop 32 junkf)).
split; [reflexivity|]. split; [exact Ef'|]. split; [change (fs_N 0) with 16384; lia|]. split; [exact FRESH|].
split. { unfold fframe_rangeA. rewrite ?KHI_eq. change (ff_size 0) with 64. subst f. repeat split; lia. }
split; [rt_solve RT RL|]. split; [exact RF'|]. split; [exact BODY|]. split; [exact SHC|].
rewrite FLG. change (ff_size 0) with 64. change (64 / 8) with 8. exact MU2.
Qed.

End Walk.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QQwg QKTr.
Import QJBH.
Import QZzg QTVW QbcP_c1 Q61C QWRO Qu4g QFQR QmP7 QKBN QN4c QNQk.Mq6 QpY2.Mqb QTVW.Mq7 QNQk.Mq8 QOJv.Mqa.
Import QlES.
Import ListNotations.
Import Qc6I.Exc. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition mmap_or_die_entry : Z := 0x77414.
Definition MMAPANON_STACK : Z := 320.

Lemma apply_unit_writes : forall ws m lo,
(forall w, In w ws -> length (snd w) = 1%nat) ->
map (fun w => bv_unsigned (fst w)) ws = zrange lo (length ws) ->
0 <= lo -> lo + Z.of_nat (length ws) <= 2^64 ->
(forall x : word, lo <= bv_unsigned x < lo + Z.of_nat (length ws) -> exists b, apply_writes m ws x = Some b)
/\ (forall x : word, ~ (lo <= bv_unsigned x < lo + Z.of_nat (length ws)) -> apply_writes m ws x = m x).
Proof.
induction ws as [|[aw bs] ws IH]; intros m lo Hu Hm Hlo Hhi; cbn [apply_writes length map zrange] in *.
- split; [intros x Hx; lia| intros x _; reflexivity].
- injection Hm as Haw Hm. cbn [fst snd] in *.
pose proof (Hu (aw, bs) ltac:(left; reflexivity)) as Hl. cbn [snd] in Hl.
destruct bs as [|b [|b' bs]]; try discriminate.
assert (Eaw : aw = wa lo) by (apply bv_eq; rewrite wa_unsigned by lia; exact Haw).
destruct (IH (write_to_mem m aw [b]) (lo + 1) ltac:(intros w Hw; apply Hu; right; exact Hw) Hm ltac:(lia) ltac:(lia)) as [IH1 IH2].
assert (W1 : forall x : word, write_to_mem m aw [b] x = if bv_unsigned x =? lo then Some b else m x).
{ intros x. rewrite Eaw. rewrite (write_to_mem_spec [b] m lo x) by (cbn [length]; lia). cbn [length].
pose proof (bv_unsigned_in_range 64 x).
destruct (Z.eqb_spec (bv_unsigned x) lo) as [E|NE].
- rewrite E. replace ((lo <=? lo) && (lo <? lo + Z.of_nat 1)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
rewrite Z.sub_diag. reflexivity.
- destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? lo + Z.of_nat 1)) eqn:C; [| reflexivity].
apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2. lia. }
split.
+ intros x Hx. destruct (Z.eq_dec (bv_unsigned x) lo) as [E|NE].
* rewrite (IH2 x) by lia. rewrite W1, E, Z.eqb_refl. exists b. reflexivity.
* apply IH1. lia.
+ intros x Hx. rewrite (IH2 x) by lia. rewrite W1. destruct (Z.eqb_spec (bv_unsigned x) lo); [lia| reflexivity].
Qed.

Lemma zrange_length : forall lo k, length (zrange lo k) = k.
Proof. intros lo k. revert lo. induction k; intros; cbn; [reflexivity| rewrite IHk; reflexivity]. Qed.

Section S.
Context {BAND : Band}.
Variables (L : lvp) (RE : aentry) (X : rlay).
Local Notation atn := (at_nodeA L asegs).

Lemma sh_lo_SH a : QKTr.sh_lo a = SH a.
Proof. unfold QKTr.sh_lo, SH, kShadowOffset, A_SHADOW_OFS. lia. Qed.
Lemma sh_hi_SH a n : a mod 8 = 0 -> n mod 8 = 0 -> 0 < n -> QKTr.sh_hi a n = SH a + n / 8.
Proof. intros Ha Hn Hp. unfold QKTr.sh_hi, SH, kShadowOffset, A_SHADOW_OFS. Z.div_mod_to_equations. lia. Qed.

Definition map_anon_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(N : Z) (avoid : list (Z * Z)) (lo : Z) (m : mem) (ans : ansA) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ match ans with
| AErr => a0 = wz 0 /\ munch [(bv_unsigned sp - MMAPANON_STACK, bv_unsigned sp)] m m'
| AOk mb => a0 = wz mb
/\ mb mod 4096 = 0 /\ appr mb N /\ mb + N <= band_lo /\ avoids mb N avoid = true
/\ munch [(bv_unsigned sp - MMAPANON_STACK, bv_unsigned sp); (mb, mb + N); (SH mb, SH mb + N / 8)] m m'
/\ rw_cells asegs m' mb [CB (Z.to_nat N) (repeat (b8 0) (Z.to_nat N))]
/\ (exists shj, rw_cells asegs m' (SH mb) [CB (Z.to_nat (N / 8)) shj])
end.

Lemma mmap_or_die_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc m (N lo : Z) (avoid : list (Z * Z)) (name : word),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - MMAPANON_STACK ->
N mod 4096 = 0 -> 0 < N -> N <= 2^40 ->
(forall b, (0 < b /\ b + N <= 2^64) -> avoids b N avoid = true -> appr b N /\ b + N <= band_lo) ->
(forall b o, (0 < b /\ b + N <= 2^64) -> avoids b N avoid = true -> In o (rlay_objs RE X) -> b + N <= fst o \/ fst o + snd o <= b) ->
impl asegs atn (enode (NMmap 0 N PROT_RW FL_ANON) (dec_anonA N avoid))
(epost (map_anon_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc N avoid lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz N) name a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz mmap_or_die_entry) fc None m (seg_rom asegs)).
Proof.
intros until name; intros RT RL MI ST CEIL LO NAL N0 N40 AVK AVO.
pose proof CEIL as CEIL'. idtac. unfold MMAPANON_STACK in *.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
rtc RT 18%nat K18. rtc RT 8%nat K8. unfold mmap_or_die_entry.
apply impl_enode.
carve_frame 48%nat ST.
do 5 step.
step. step. step. step.
step.
clear K18 K8.
step. if_lit.
step. step. step. if_lit.
stp. stp. stp. stp.
rewrite (unsigned_lit (N + 4095)) by lia. rewrite land_pagemask by lia.
replace (N + 4095 - (N + 4095) mod 4096) with N by (Z.div_mod_to_equations; lia).
step. stf. step. step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT1 : RTconst RE X mm) end.
{ eapply RTconst_stack; [exact RT| exact RL| exact MU| exact WM|]. constructor; [cbn [fst]; lia| constructor]. }
call_sp (get_named_mapping_fd_spec _ _); try eassumption; [lia|]. subst. clear RT1. rename POST into RT1.
match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
stp.
step. step. step. step. step.
step. step.
step_ecall.
split. { cbn [at_nodeA]. at_node_solve. }
intros rsp ans Hdec. destruct ans as [|mb].
-
apply dec_anonA_err_inv in Hdec. subst rsp. sys_nret.
change (errno_ret ENOMEM) with (wz (-12)).
step.
step. step. step.
stp. stp. step. if_lit.
step. if_lit.
stp. step.
step. step. stf. step.
step. step.
stp. stp. step. if_lit.
step.
unfold_cond. rewrite (unsigned_lit (bv_unsigned sp + -40)) by lia. if_lit.
stp. stp.
stp. step.
step. if_lit.
stp. step. step. if_lit.
step. step.
step. do 4 step. step. step.
release_frame FR ST (bv_unsigned sp). clear RT1.
apply evt_done. unfold map_anon_post. do 16 eexists. split; [reflexivity|].
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [| split; [reflexivity| exact MU]].
eapply RTconst_munch; [exact RT| exact MU| exact WM|]. constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor].
-
apply dec_anonA_ok_inv in Hdec as (ws & -> & Emb & GOK & AV & WS & COV).
rewrite (mmap_len_aligned N) in * by exact NAL.
cbn [eff_ret] in Emb. pose proof (bv_unsigned_in_range 64 (wz mb)) as MBR. unfold bv_modulus in MBR. change (2 ^ Z.of_N 64) with (2^64) in MBR. rewrite <- Emb in MBR.
unfold grant_ok in GOK. apply andb_prop in GOK as [GOK G3]. apply andb_prop in GOK as [G1 G2].
apply Z.eqb_eq in G1. apply Z.ltb_lt in G2. apply Z.leb_le in G3. unfold page_size in G1. idtac.
rewrite sh_lo_SH in COV. rewrite (sh_hi_SH mb N) in COV by (try lia; Z.div_mod_to_equations; lia).
replace (SH mb + N / 8 - SH mb) with (N / 8) in COV by lia.
assert (LWS : length ws = Z.to_nat (N / 8)) by (rewrite <- (zrange_length (SH mb)), <- COV, length_map; reflexivity).
rewrite (mmap_len_aligned N) in G3 by exact NAL. destruct (AVK mb ltac:(rewrite grant_ceil_val in G3; lia) AV) as [GK GB]. apply appr_to_lia in GK; [| lia| lia].
assert (SHB : 0x7fff8000 <= SH mb /\ SH mb + N / 8 <= 0x10007fff8000) by (clear -G1 G2 G3 N0 GB; unfold SH, A_SHADOW_OFS; Z.div_mod_to_equations; lia).
sys_nret.
lazymatch goal with |- context [apply_unmaps ?mm []] => change (apply_unmaps mm []) with mm end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (apply_writes (apply_zeros ?mz [(?A1, wz ?n1)]) ws) _) =>
change (apply_zeros mz [(A1, wz n1)]) with (apply_zeros mz [(wa mb, wz N)]);
assert (Hza : 0 <= mb < 2^64) by lia; assert (Hzn : 0 <= N < 2^64) by lia; assert (Hzan : mb + N <= 2^64) by lia;
apply (munch_weaken _ [(bv_unsigned sp - 320, bv_unsigned sp); (mb, mb + N); (SH mb, SH mb + N / 8)]) in MU; [| unfold sub_fp; cbn [outside]; intros; tauto];
transport_zeros asegs mz mb N Hza Hzn Hzan;
pose proof (rw_cells_zeros_new asegs mz mb N Hza Hzn Hzan) as ZNEW;
remember (apply_zeros mz [(wa mb, wz N)]) as m2 eqn:Heqm; clear Heqm Hza Hzn Hzan
end.
Unshelve. 2: (apply a_ro_addr_false; lia).

destruct (apply_unit_writes ws m2 (SH mb) ltac:(intros w Hw; unfold wshape_ok in WS; rewrite forallb_forall in WS;
pose proof (WS w Hw) as B; apply andb_prop in B as [_ B]; apply Nat.eqb_eq in B; exact B)
ltac:(rewrite LWS; exact COV) ltac:(lia) ltac:(rewrite LWS, Z2Nat.id by lia; lia)) as [PRES SAME].
rewrite LWS, Z2Nat.id in PRES, SAME by lia.
assert (MU23 : munch [(SH mb, SH mb + N / 8)] m2 (apply_writes m2 ws)) by (intros xw Hx; apply SAME; cbn [outside] in Hx; lia).
assert (WM23 : wmono asegs m2 (apply_writes m2 ws)).
{ intros xw Hx. pose proof (bv_unsigned_in_range 64 xw) as XR.
destruct (Z.lt_ge_cases (bv_unsigned xw) (SH mb)) as [L1|L1]; [unfold wview in *; rewrite SAME by lia; exact Hx|].
destruct (Z.lt_ge_cases (bv_unsigned xw) (SH mb + N / 8)) as [L2|L2]; [| unfold wview in *; rewrite SAME by lia; exact Hx].
destruct (PRES xw ltac:(lia)) as [b Hb]. unfold wview. rewrite Hb. discriminate. }
lazymatch goal with H : mem_inv asegs m2 |- _ =>
assert (MI3 : mem_inv asegs (apply_writes m2 ws));
[ intros xw b Hb; pose proof (bv_unsigned_in_range 64 xw) as XR;
destruct (decide (SH mb <= bv_unsigned xw < SH mb + N / 8)) as [IN|OUT];
[ apply a_ro_addr_false; lia | rewrite SAME in Hb by exact OUT; exact (H xw b Hb) ]
| clear H ] end.
transport_after_call asegs m2 (apply_writes m2 ws) MU23 WM23.
assert (SHJ : hjunk (apply_writes m2 ws) (SH mb) (SH mb + Z.of_nat (Z.to_nat (N / 8)))).
{ rewrite Z2Nat.id by lia. split; [lia|]. split; [lia|]. intros y Hy. destruct (PRES (wa y) ltac:(rewrite wa_unsigned by lia; lia)) as [b Hb]. exists b. exact Hb. }
destruct (hjunk_cells _ _ _ SHJ) as [shj SHC]. clear SHJ.
remember (apply_writes m2 ws) as m3 eqn:Heqm3. clear Heqm3 PRES SAME MU23 WM23.
step.
step. step. step.
stp. stp. step.
unfold_cond. rewrite <- ?Emb, ?(unsigned_lit mb) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit mb) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? mb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. step. stf. step.
step. step.
stp. stp. step.
unfold_cond. rewrite (unsigned_lit mb) by lia. if_lit.
step. rewrite v_sltu_b2z. rewrite (unsigned_lit mb) by lia. fold_closed_in_goal.
replace (18446744073709547520 <? mb) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
step.
step. if_lit.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RT2 : RTconst RE X mm) end.
{ eapply RTconst_munch; [exact RT| exact MU| exact WM|].
constructor; [apply rt_avoid_stack; [exact RL| lia]| constructor; [| constructor; [| constructor]]].
- intros y Hy Fy. cbn [fst snd] in Hy. destruct (fp_RTconst_where RE X y Fy) as [LOW|(o & Ho & [O1 O2])]; [lia|].
destruct (AVO mb o ltac:(lia) AV Ho); lia.
- intros y Hy Fy. cbn [fst snd] in Hy. destruct (fp_RTconst_where RE X y Fy) as [LOW|(o & Ho & [O1 O2])]; [lia|].
pose proof (rlay_obj_facts RE X o RL Ho) as (_ & OK & _). rewrite ?KHI_eq in OK. lia. }
step. call0 (increase_total_mmap_spec RE X); [exact RT2| assumption|].
step. do 4 step. step. step.
release_frame FR ST (bv_unsigned sp).
apply evt_done. unfold map_anon_post. do 16 eexists. split; [first [reflexivity| rewrite <- Emb; reflexivity]|].
split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact RT2|].
split; [first [reflexivity| rewrite <- Emb; reflexivity]|]. split; [exact G1|]. split; [apply appr_of_lia; exact GK|]. split; [exact GB|]. split; [exact AV|].
split; [exact MU|]. split; [exact ZNEW| exists shj; exact SHC].
Qed.
End S.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc27 Q13u QHig Qc6I QJFf QBrp QDM6 QVsB Qsn5 QwAs.Mq2.
Import QCiC Q6sh QKTr.
Import QJBH.
Import QZzg QTVW Q61C QWRO QFQR QmP7 QKBN QNQk.Mq6 QTVW.Mq7 QOJv.Mqb.
Import QlES. Local Ltac QbcP_c1.small_offset k ::= QbcP_c1.mkr__small_offset_0 k. Local Ltac QoSL.solve_load ::= QbcP_c1.mkr__solve_load_1. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Local Set Keyed Unification.

Import ListNotations.
Open Scope Z_scope.

Local Notation wz := (Z_to_bv 64).
Local Notation b8 := (Z_to_bv 8).
Local Notation mem := (word -> option byte) (only parsing).

Definition PZ_STACK : Z := 640.

Section S.
Context {BAND : Band}.
Variables (RE : aentry) (X : rlay).

Definition pz_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(addr size lo : Z) (m : mem) (s : PStateA) (r : unit) (s' : PStateA) (ms' : machine_state) : Prop :=
exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
ms' = MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ s' = s
/\ munch [(bv_unsigned sp - PZ_STACK, bv_unsigned sp); (SH addr, SH addr + size / 8)] m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ RTconst RE X m'
/\ rw_cells asegs m' (SH addr) [CB (Z.to_nat (size / 8)) (repeat (b8 0) (Z.to_nat (size / 8)))].

Definition poison_zero_stmt (L : lvp) : Prop :=
forall (ra sp gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (addr size lo : Z) (s : PStateA) (junk : list byte),
RTconst RE X m -> rlay_ok RE X -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> band_lo <= lo -> lo <= bv_unsigned sp - PZ_STACK ->
addr mod 8 = 0 -> size mod 8 = 0 -> 0 < size -> KHI <= addr -> addr + size <= 2^47 ->
rw_cells asegs m (SH addr) [CB (Z.to_nat (size / 8)) junk] ->
aimplT (at_nodeA L asegs) (clear_shadow addr size) s (pz_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m s)
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz addr) (wz size) (wz 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz poison_shadow_entry) fc None m (seg_rom asegs)).
End S.
End Mqc.

From Stdlib Require Import ZArith Lia.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc27.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc27. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0z1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0z1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZzg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZzg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFQR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFQR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNQk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNQk.Mq6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpY2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpY2.Mqc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcfN.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcfN.Mq4. Local Ltac QoSL.solve_store ::= QoSL.mkr__solve_store_9. Local Ltac QwAs.Mq2.zs_idioms ::= QwAs.Mq2.mkr__zs_idioms_3. Local Ltac QwAs.Mq2.zs_idioms_in H ::= QwAs.Mq2.mkr__zs_idioms_in_4 H. Local Ltac QwAs.Mq2.zs_wrap e ::= QwAs.Mq2.mkr__zs_wrap_1 e. Local Ltac QwAs.Mq2.zs_wrap_in e H ::= QwAs.Mq2.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module LF.
Import Ltac2.

Ltac2 is_enc_atom (a : constr) : bool :=
match Constr.Unsafe.kind a with
| Constr.Unsafe.App f _ =>
if Constr.equal f constr:(zhigh) then true else if Constr.equal f constr:(zhull) then true
else Constr.equal f constr:(zsel)
| _ => false
end.
Ltac2 rel_prune_gen (sec : bool) (hops : int) (cap : int) (disj : bool) : unit :=
let ops := RL.ops () in
let hs := Control.hyps () in
let facts := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some _ => None
| None => if Bool.or sec (RL.is_local id) then (if SF2.arith_logic ty then Some (id, ty) else None) else None
end) hs in

let lets := List.map_filter (fun h => let (id, body, ty) := h in
match body with
| Some b => Some (RL.add_atom (Control.hyp id) (RL.atoms ops [] b))
| None => None
end) hs in
let step g := List.fold_left (fun acc ap => if RL.meets ap g then List.fold_left (fun acc a => RL.add_atom a acc) acc ap else acc) g
(List.append lets (List.map (fun f => let (_, p) := f in RL.atoms ops [] p) facts)) in
let rec close n g := if Int.equal n 0 then g else close (Int.sub n 1) (step g) in
let g0 := RL.atoms ops [] (Control.goal ()) in

let g0 := match g0 with
| [] => List.fold_left (fun g f => let (_, p) := f in List.fold_left (fun g a => RL.add_atom a g) g (RL.atoms ops [] p))
[] (List.firstn (if Int.le (List.length facts) 4 then List.length facts else 4) (List.rev facts))
| _ :: _ => g0
end in
let g := close hops g0 in

let drop := List.map_filter (fun f => let (id, p) := f in
let ap := RL.atoms ops [] p in
if List.exist is_enc_atom ap then Some id
else if Bool.or disj (SF2.plain_arith true p) then (if RL.meets ap g then None else Some id)
else Some id) facts in
let ndisj := List.length (List.filter (fun f => let (id, p) := f in
if List.exist (fun d => Ident.equal d id) drop then false else Bool.neg (SF2.plain_arith true p)) facts) in
if Int.gt (Int.sub (List.length facts) (List.length drop)) cap then Control.zero (Tactic_failure None) else
if Int.gt ndisj 4 then Control.zero (Tactic_failure None) else
match drop with [] => () | _ :: _ => Std.clear drop end.
Ltac rel_prune_local2 := ltac2:(Control.enter (fun () => rel_prune_gen false 2 100000 false)).
Ltac rel_prune_local4 := ltac2:(Control.enter (fun () => rel_prune_gen false 4 100000 false)).
Ltac rel_prune_sec2 := ltac2:(Control.enter (fun () => rel_prune_gen true 2 100000 false)).
Ltac rel_prune_sec4 := ltac2:(Control.enter (fun () => rel_prune_gen true 4 100000 false)).
Ltac rel_prune_disj2 := ltac2:(Control.enter (fun () => rel_prune_gen false 2 30 true)).
Ltac rel_prune_disj4 := ltac2:(Control.enter (fun () => rel_prune_gen false 4 45 true)).

Ltac2 zlf_arith_goal () : unit := if SF2.arith_logic (Control.goal ()) then () else Control.zero (Tactic_failure None).
Ltac zlf_arith_goal := ltac2:(Control.enter zlf_arith_goal).

Ltac2 zlf_no_enc () : unit :=
let ops := RL.ops () in
if List.exist (fun h => let (_, body, ty) := h in
match body with
| Some _ => false
| None => if SF2.arith_logic ty then List.exist is_enc_atom (RL.atoms ops [] ty) else false
end) (Control.hyps ())
then Control.zero (Tactic_failure None) else ().
Ltac zlf_no_enc := ltac2:(Control.enter zlf_no_enc).
End LF.
Ltac zlf_no_enc := LF.zlf_no_enc.
Ltac zlf_arith_goal := LF.zlf_arith_goal.
Ltac rel_prune_local2 := LF.rel_prune_local2.
Ltac rel_prune_local4 := LF.rel_prune_local4.
Ltac rel_prune_sec2 := LF.rel_prune_sec2.
Ltac rel_prune_sec4 := LF.rel_prune_sec4.
Ltac rel_prune_disj2 := LF.rel_prune_disj2.
Ltac rel_prune_disj4 := LF.rel_prune_disj4.

Ltac zify_goal_dm :=
repeat match goal with
| |- context [Z.div ?x ?y] => zify_new_dm x y
| |- context [Z.modulo ?x ?y] => zify_new_dm x y
end.
Ltac goal_has_dm := match goal with |- context [Z.div _ _] => idtac | |- context [Z.modulo _ _] => idtac end.

Definition zlf_done (x y : Z) : Prop := True.
Lemma zlf_div_spec : forall x d, 0 < d -> d * (x / d) <= x < d * (x / d) + d.
Proof. intros x d Hd. pose proof (Z.div_mod x d ltac:(lia)). pose proof (Z.mod_pos_bound x d Hd). lia. Qed.
Lemma zlf_mod_spec : forall x d, 0 < d -> x = d * (x / d) + x mod d /\ 0 <= x mod d < d.
Proof. intros x d Hd. split; [apply Z.div_mod; lia| apply Z.mod_pos_bound; exact Hd]. Qed.
Ltac zlf_pos_lit y := lazymatch y with Zpos _ => idtac end.
Ltac zlf_new x y :=
lazymatch goal with
| _ : zlf_done x y |- _ => fail
| _ => zlf_pos_lit y; pose proof (zlf_div_spec x y eq_refl); pose proof (zlf_mod_spec x y eq_refl); pose proof (I : zlf_done x y)
end.
Ltac zify_divlit :=
repeat match goal with
| |- context [Z.div ?x ?y] => zlf_new x y
| |- context [Z.modulo ?x ?y] => zlf_new x y
| _ : context [Z.div ?x ?y] |- _ => zlf_new x y
| _ : context [Z.modulo ?x ?y] |- _ => zlf_new x y
| _ := context [Z.div ?x ?y] |- _ => zlf_new x y
| _ := context [Z.modulo ?x ?y] |- _ => zlf_new x y
end.

Ltac zlf_prune2 := rel_prune_local2.
Ltac zlf_prune4 := rel_prune_local4.
Ltac lia_pruned := zlf_arith_goal; first [ Qo9G.term_slim ltac:(zlf_prune2; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| zlf_prune4;
first [ Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zlf_no_enc; zify_divlit; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ] ].

Ltac lia_fast := first [ lia_pruned
| zify_prune;
first [ Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(zify_has_divmod; Zify.zify; xlia zchecker) ]
| Qo9G.term_slim ltac:(Zify.zify; xlia zchecker) ].

Ltac tslia_fast := first [ exact I
| sf_unhide; lia_pruned
| Qo9G.term_slim ltac:(zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Q0z1.tslia ].

Ltac solve_cond_base_p :=
first [ reflexivity
| apply Z.ltb_lt; lia_pruned | apply Z.ltb_ge; lia_pruned
| apply Z.leb_le; lia_pruned | apply Z.leb_gt; lia_pruned
| apply Z.eqb_eq; lia_pruned | apply Z.eqb_neq; lia_pruned ].
Ltac solve_cond_rec_p :=
lazymatch goal with
| |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); solve_cond_rec_p
| |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); solve_cond_rec_p
| _ => solve_cond_base_p
end.
Ltac solve_cond_p := unfold_cond; fold_lit_ux; solve_cond_rec_p.
Ltac if_true_p :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond_p]
end.
Ltac if_false_p :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond_p]
end.

Ltac zlf_no_vars c := match c with context [?x] => is_var x; fail 1 | _ => idtac end.
Ltac if_true_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
zlf_no_vars c; replace c with true; [cbv iota| symmetry; unfold_cond; fold_lit_ux; reflexivity]
end.
Ltac if_false_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
zlf_no_vars c; replace c with false; [cbv iota| symmetry; unfold_cond; fold_lit_ux; reflexivity]
end.
Ltac if_lit_fast := first [ if_true_lit | if_false_lit | if_true_p | if_false_p | if_true | if_false ].

Ltac sfp_fast := first [ apply Z.le_refl | lia_pruned ].

Ltac lia_pruned_disj := zlf_arith_goal;
first [ Qo9G.term_slim ltac:(rel_prune_disj2; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker)
| Qo9G.term_slim ltac:(rel_prune_disj4; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker) ].

Ltac st_avoid_solve_fast :=
lazymatch goal with
| |- st_avoid (?lo, _) =>
lazymatch lo with
| context [rl_T _] => eapply st_avoid_T; [eassumption| cbn [fst snd]; first [ lia_pruned | lia ]| cbn [fst snd]; first [ lia_pruned | lia ]]
| _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; first [ lia_pruned | unfold prim_lo, prim_hi in *; lia ]
end
| |- _ => apply st_avoid_above; cbn [fst snd]; unfold A_ERRNO; first [ lia_pruned | unfold prim_lo, prim_hi in *; lia ]
end.

Ltac if_lit_lit := first [ if_true_lit | if_false_lit | if_true | if_false ].

Ltac addr_eq_tac_w :=
lazymatch goal with
| |- @eq nat _ _ => fail
| |- _ => symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ]
end.

Module SF2L.
Import Ltac2.
Ltac2 rec clean2 (bad : constr list) (kd : constr list) (c : constr) : bool :=
match Constr.Unsafe.kind c with
| Constr.Unsafe.App f args =>
if List.exist (Constr.equal f) kd then
(if Int.equal (Array.length args) 2 then
(match Q0z1.SF2.vars_of [] (Array.get args 1) with
| [] => clean2 bad kd (Array.get args 0) | _ :: _ => false end)
else false)
else if List.exist (Constr.equal f) bad then false
else if clean2 bad kd f then Array.fold_left (fun b a => if b then clean2 bad kd a else false) true args else false
| Constr.Unsafe.Constant _ _ => if List.exist (Constr.equal c) bad then false else true
| Constr.Unsafe.Prod b body => if clean2 bad kd (Constr.Binder.type b) then clean2 bad kd body else false
| Constr.Unsafe.Lambda _ _ => false
| Constr.Unsafe.Case _ _ _ _ _ => false
| Constr.Unsafe.LetIn _ _ _ => false
| _ => true
end.
Ltac2 hide_poison2 () : unit :=
let bad := Q0z1.SF2.bad_heads () in
let kd := [constr:(Z.div); constr:(Z.modulo)] in
let kk := Q0z1.SF2.sk_mk () in
List.iter (fun h => let (id, body, ty) := h in
match body with
| Some _ => ()
| None =>
if Q0z1.SF2.al_k kk ty then
(if (if Q0z1.SF2.plain_k kk false ty then clean2 bad kd ty else false) then ()
else let c := Control.hyp id in
ltac1:(c |- lazymatch type of c with ?T => change T with (Q0z1.sf_hide T) in c end) (Ltac1.of_constr c))
else ()
end) (Control.hyps ()).
Ltac2 hide_poison2_1 () : unit := Control.enter hide_poison2.
End SF2L.
Ltac sf_hide_poison_divlit := ltac2:(SF2L.hide_poison2_1 ()).
