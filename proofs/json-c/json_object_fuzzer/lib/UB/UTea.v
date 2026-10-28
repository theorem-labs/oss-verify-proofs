(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG Qnhz QO3A Q7m0 QSpR QuJV QCPB QH7x QXup UEQM Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek UC8c Qsw7 QJjn UBpZ UT7i Uv6q UD4E UzWc Um2h UDgQ UTru UM4C UgTW Qio9 QHXC Qfe5 QId5 Uuoa ULch UwKH UMJA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsRG.Mq0 Qnhz.Mq0 QsRG QO3A Q7m0 QSpR.Mq4 QuJV QCPB.Mq0 QH7x.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UC8c.Mq0.
Import Qsw7 QJjn.
Import UBpZ UT7i Uv6q UD4E.
Import UzWc.
Import Um2h UDgQ UTru UM4C UgTW.Mq0.
Import Qio9 QHXC Qfe5 QId5.
Import Uuoa ULch UwKH UMJA.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition HEXZ : list Z := [48;49;50;51;52;53;54;55;56;57;97;98;99;100;101;102;65;66;67;68;69;70].
Definition HEXB : list byte := map (Z_to_bv 8) HEXZ.

#[using="Type"] Lemma ro_hexb : ro_bytes rsegs 0x12b12 HEXB.
Proof. cbn [HEXB HEXZ map ro_bytes]. repeat split; vm_compute; reflexivity. Qed.

#[using="Type"] Lemma mask_clear_ctrl : forall c : byte,
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
branch_taken BC_EQ (alu64 ALU_AND (alu64 ALU_SRL (Z_to_bv 64 140754668238592) (Z_to_bv 64 (bv_unsigned c))) (Z_to_bv 64 1))
(Z_to_bv 64 0) = true.
Proof.
intros c Hc Hn. pose proof (bv_unsigned_in_range 8 c) as R.
assert (E : exists k, bv_unsigned c = Z.of_nat k /\ (k < 32)%nat) by (exists (Z.to_nat (bv_unsigned c)); lia).
destruct E as (k & E & Hk). rewrite E in *.
do 32 (destruct k as [|k]; [first [exfalso; apply Hn; cbn; tauto | vm_compute; reflexivity] |]). lia.
Qed.

#[using="Type"] Lemma u_and15 : forall x : word, bv_unsigned (alu64 ALU_AND x (Z_to_bv 64 15)) = bv_unsigned x mod 16.
Proof.
intros x. rewrite QsjA.alu_and. unfold QsjA.v_and. pose proof (bv_unsigned_in_range 64 x) as R.
change (bv_unsigned (Z_to_bv 64 15)) with 15. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
change (2 ^ 4) with 16. apply unsigned_lit. unfold bv_modulus in R. cbn in R. pose proof (Z.mod_pos_bound (bv_unsigned x) 16). lia.
Qed.
#[using="Type"] Lemma u_srl4 : forall x : word, bv_unsigned (alu64 ALU_SRL x (Z_to_bv 64 4)) = bv_unsigned x / 16.
Proof.
intros x. rewrite QsjA.alu_srl. unfold QsjA.v_srl. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
change (bv_unsigned (Z_to_bv 64 4) mod 64) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
apply unsigned_lit. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

#[using="Type"] Lemma room_test : forall cap bpos : Z, 0 <= bpos <= cap -> cap < 2^31 ->
bv_lts (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 (cap - bpos))) (low32 (Z_to_bv 64 0))))
(Z_to_bv 64 7) = Z.ltb (cap - bpos) 7.
Proof.
intros cap bpos H1 H2.
rewrite QsjA.w_addw. unfold QsjA.v_addw. rewrite !unsigned_lit by lia. rewrite Z.add_0_r, swrap32_id by lia.
unfold bv_lts. rewrite !s64_of_Z by lia. reflexivity.
Qed.

#[using="Type"] Lemma add_lit : forall a b : Z, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb. rewrite QsjA.alu_add. unfold QsjA.v_add. rewrite (unsigned_lit a), (unsigned_lit b) by lia. reflexivity. Qed.

#[using="Type"] Lemma chk_nz_core : forall a s : Z, 0 < a < 2^64 -> 0 < s < 2^64 ->
bv_eqb (alu64 ALU_SLTU (Z_to_bv 64 0) (Z_to_bv 64 a)) (alu64 ALU_SLTU (Z_to_bv 64 s) (Z_to_bv 64 1)) = false.
Proof.
intros a s Ha Hs.
rewrite (QsjA.alu_sltu (Z_to_bv 64 0) (Z_to_bv 64 a)), (QsjA.alu_sltu (Z_to_bv 64 s) (Z_to_bv 64 1)).
unfold QsjA.v_sltu, QsjA.c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
replace (s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma chk_pofs_core : forall a b s : Z, 0 <= a <= s -> s < 2^64 -> 0 <= b < 2^63 ->
bv_eqb (alu64 ALU_XOR (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 s) (Z_to_bv 64 a))
(alu64 ALU_SLT (Z_to_bv 64 b) (Z_to_bv 64 0))) (Z_to_bv 64 1)) (Z_to_bv 64 0) = false.
Proof.
intros a b s Ha Hs Hb.
rewrite (QsjA.alu_sltu (Z_to_bv 64 s) (Z_to_bv 64 a)), (QsjA.alu_slt (Z_to_bv 64 b) (Z_to_bv 64 0)).
unfold QsjA.v_sltu, QsjA.v_slt, QsjA.c_ltu, QsjA.c_lts, bv_ltu, bv_lts.
rewrite !unsigned_lit by lia. rewrite !s64_of_Z by lia.
replace (s <? a) with false by (symmetry; apply Z.ltb_ge; lia).
replace (b <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma chk_addw_nowrap : forall bpos k : Z, 0 <= bpos -> 0 <= k -> bpos + k < 2^31 ->
bv_lts (sext 64 (alu32 ALU_ADD (low32 (SX2.ext_val true 0 4 (Z_to_bv 64 bpos))) (low32 (Z_to_bv 64 k))))
(SX2.ext_val true 0 4 (Z_to_bv 64 bpos)) = false.
Proof.
intros bpos k H1 H2 H3.
rewrite !ext_val_sx_id by (first [cbn; lia | cbn; rewrite unsigned_lit by lia; lia]).
rewrite QsjA.w_addw. unfold QsjA.v_addw. rewrite !unsigned_lit by lia. rewrite swrap32_id by lia.
unfold bv_lts. rewrite !s64_of_Z by lia. apply Z.ltb_ge. lia.
Qed.

#[using="Type"] Lemma chk_nz_lit : forall a : Z, 0 < a < 2^64 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof. intros a Ha. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

#[using="Type"] Lemma srl4_lit : forall x : word, alu64 ALU_SRL x (Z_to_bv 64 4) = Z_to_bv 64 (bv_unsigned x / 16).
Proof.
intros x. apply bv_eq. rewrite u_srl4. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R. cbn in R.
rewrite unsigned_lit; [reflexivity|]. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

#[using="Type"] Lemma chk_nz1_core : forall s : Z, 0 < s < 2^64 ->
bv_eqb (alu64 ALU_XOR (Z_to_bv 64 1) (alu64 ALU_SLTU (Z_to_bv 64 s) (Z_to_bv 64 1))) (Z_to_bv 64 0) = false.
Proof.
intros s Hs. rewrite (QsjA.alu_sltu (Z_to_bv 64 s) (Z_to_bv 64 1)). unfold QsjA.v_sltu, QsjA.c_ltu, bv_ltu.
rewrite !unsigned_lit by lia. replace (s <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
vm_compute. reflexivity.
Qed.

#[using="Type"] Lemma chk_ltu_core : forall a s : Z, 0 <= a <= s -> s < 2^64 -> bv_ltu (Z_to_bv 64 s) (Z_to_bv 64 a) = false.
Proof. intros a s H1 H2. unfold bv_ltu. rewrite !unsigned_lit by lia. apply Z.ltb_ge. lia. Qed.

Definition snpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D h1 h2 : Z) (sb : list byte) (lo : Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, q); (D, D + 7)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ (frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo q
/\ rw_cells rsegs m' D [CB 7 (zb [92; 117; 48; 48; h1; h2] ++ Z_to_bv 8 0 :: skipn 7 sb)]
/\ ssp_cells m' canary).

#[using="Type"] Lemma snprintf_u00ccZ :
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 : word) (D : Z) (a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (h1 h2 : Z) (sb : list byte) (lo : Z) (canary : word),
0 <= q < 2^63 -> 0 <= D -> D + 7 <= 2^64 -> 0 <= h1 < 256 -> 0 <= h2 < 256 ->
rw_cells rsegs m D [CB 7 sb] -> stk rsegs m lo q -> lo <= q - SNPRINTF_DEPTH -> GLOBALS_TOP <= lo ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc -> (D + 7 <= lo \/ q <= D) -> GLOBALS_TOP <= D ->
evt rsegs (snpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D h1 h2 sb lo canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 7) (Z_to_bv 64 A_FMT_u00cc) (Z_to_bv 64 h1) (Z_to_bv 64 h2)
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Hq HD HD7 Hh1 Hh2 DST ST LOq GLO SSP MI FRM DD GD.
pose proof (snprintf_u00cc_proof ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 7) (Z_to_bv 64 A_FMT_u00cc)
(Z_to_bv 64 h1) (Z_to_bv 64 h2) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 7 h1 h2 7%nat sb lo canary) as X.
cbv zeta in X. rewrite !unsigned_lit in X by lia.
eapply evt_mono; [eapply X; try reflexivity; try assumption; try lia |].
- intros ms' P. unfold snprintf_post in P. unfold snpost.
destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & E & MU & WM & MI' & FR' & HF & ST' & RW & SSP').
rewrite !unsigned_lit in MU, ST' by lia. rewrite (Z.mod_small h1), (Z.mod_small h2) in RW by lia.
exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, Ft, fc', m'.
repeat (split; [assumption|]). exact SSP'.
Qed.

Section Esc.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HEXP : forall A LB m md, HEAPx A LB m md -> bytes_at rsegs m JHEX_SLOT (le8 (wz JHEX)).
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (pb Sa n lo : Z) (src : list byte).
Let usp := bv_unsigned sp.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis SCL : src_cls LB n usp Sa src.
Hypothesis Hn : 0 < n < 2^31.
Hypothesis HSa : 0 <= Sa /\ Sa + n < 2^64.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - 192 - 8320.
Hypothesis SPA : usp mod 16 = 0.
Hypothesis HT : usp <= hi_top S4L HIx.
Hypothesis HT63 : hi_top S4L HIx < 2^63.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis FRM : frm0 fc.

Notation esc_memx := (esc_mem HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB pb Sa lo src).
Notation esc_postx := (esc_post HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB pb Sa lo src).
Notation st_loopx := (st_loop sp gp pb Sa n).
Notation st_cx := (st_c sp gp pb Sa n).
Notation loopKx := (loopK HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB pb Sa n lo src).
Let esc_appendx := esc_append HIx MEMMOVE ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB pb Sa n lo src SRCL SCL HSa LO LOS SPA HT.
Let src_presx := src_pres_munch HIx ra sp LB pb Sa n lo src SRCL SCL Hn HSa LO LOS SPA.

Ltac prep INV HP FRc :=
pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR; unfold usp in *; unfold_consts;
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK;
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI; cbn [hl_segs S4L] in MI;
unfold escF in FRc.

Ltac hex_sc m HX H1 H2 h1 h2 c :=
lazymatch goal with
| |- evt _ _ _ => idtac
| _ => first
[ sc_cbn; eapply (sc_readbase_byte rsegs m 0x12b12 HEXB _ h2 _ HX H2);
cbv beta delta [QsRG.Mq0.v_addi]; f_equal; rewrite u_and15, unsigned_lit by lia;
pose proof (Z.mod_pos_bound (bv_unsigned c) 16); lia
| sc_cbn; eapply (sc_readbase_byte rsegs m 0x12b12 HEXB _ h1 _ HX H1);
cbv beta delta [QsRG.Mq0.v_addi]; f_equal; rewrite u_srl4, unsigned_lit by lia;
pose proof (Z.div_pos (bv_unsigned c) 16); pose proof (Z.div_lt_upper_bound (bv_unsigned c) 16 2); lia
| sc_cbn; rewrite u_srl4, !unsigned_lit by lia;
pose proof (Z.div_pos (bv_unsigned c) 16); pose proof (Z.div_lt_upper_bound (bv_unsigned c) 16 2); lia
| sc_cbn; cbn [branch_taken]; rewrite srl4_lit, (unsigned_lit (bv_unsigned c)) by lia;
pose proof (Z.div_pos (bv_unsigned c) 16); pose proof (Z.div_lt_upper_bound (bv_unsigned c) 16 2);
rewrite add_lit by lia; first [ apply chk_nz1_core; lia | apply chk_ltu_core; lia ]
| idtac ]
end.

Ltac fast_sc :=
lazymatch goal with
| |- evt _ _ _ => idtac
| _ => sc_cbn; cbn [branch_taken]; rewrite ?add_lit by lia; first
[ rewrite room_test by lia; first [ apply Z.ltb_ge; lia | apply Z.ltb_lt; lia ]
| apply chk_nz_core; lia
| apply chk_pofs_core; lia
| apply chk_addw_nowrap; lia
| apply chk_nz_lit; lia ]
end.

#[using="MEMMOVE HEXP usp SRCL SCL Hn HSa LO LOS SPA HT HT63 esc_appendx src_presx"] Lemma esc_ctrl_tail :
forall x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md pos (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= pos < n ->
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_cx 0x27130 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned c) F' fc' m pos) md) T.
Proof.
intros until T. intros INV FS FR Hpos C32 CNS IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_c. prep INV HP FRc.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
pose proof (HEXP _ _ _ _ HP) as JH. unfold JHEX_SLOT, JHEX in JH.
pose proof (ro_bytes_at rsegs m 0x12b12 HEXB MI ltac:(lia) ltac:(cbn; lia) ro_hexb) as HX.
destruct (nth_error HEXB (Z.to_nat (bv_unsigned c / 16))) as [h1|] eqn:H1; [| apply nth_error_None in H1; cbn in H1; lia].
destruct (nth_error HEXB (Z.to_nat (bv_unsigned c mod 16))) as [h2|] eqn:H2; [| apply nth_error_None in H2; cbn in H2; lia].
unfold JHEX_SLOT in FRc.
pose proof (bv_unsigned_in_range 8 h1) as R1. pose proof (bv_unsigned_in_range 8 h2) as R2. unfold bv_modulus in R1, R2. cbn in R1, R2.
apply rz_evt; [exact MOK|].
symb_run 30%nat [0x5514c]%Z [false; false; false; false] extra [Z_to_bv 64 (bv_unsigned h1); Z_to_bv 64 (bv_unsigned h2)].
all: hex_sc m HX H1 H2 h1 h2 c.

pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & CAN3). cbn [hl_got_guard hl_guard hl_tp S4L] in CAN1, CAN2, CAN3.
pose proof (ssp_cells_of_bytes_at m g CAN1 CAN2) as SSP.

lazymatch type of FRc with rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
change (rw_cells rsegs m A ([c1; c2; c3; c4; c5] ++ ([c6] ++ rest))) in FRc end.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRc as [FRa FRbc]. cbn [cells_size csize Nat.add] in FRbc. change (Z.of_nat 33) with 33 in FRbc.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FRbc as [FRb FRd]. cbn [cells_size csize Nat.add] in FRd. change (Z.of_nat 7) with 7 in FRd.
replace (bv_unsigned sp + -144 + 33) with (bv_unsigned sp + -111) in FRb, FRd by lia.
replace (bv_unsigned sp + -111 + 7) with (bv_unsigned sp + -104) in FRd by lia.
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi, Hbhi. unfold ERRNO in ERR.
assert (SRCk : True -> bytes_at rsegs m Sa src) by (intros _; exact SRC). clear SRC.
pose proof (munch_refl [(lo, bv_unsigned sp + -144); (bv_unsigned sp + -111, bv_unsigned sp + -104)] m) as MU.
pose proof (wmono_refl rsegs m) as WM.
assert (LSB : length sbf = 7%nat) by (destruct FRb as [[[W _] _] _]; cbn in W; lia).
call (snprintf_u00ccZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned h1) (bv_unsigned h2) sbf lo g);
[ first [ exact FRb | exact ST | exact SSP | exact MI | exact FR | unfold SNPRINTF_DEPTH, GLOBALS_TOP in *; lia ] .. | ].

match goal with |- evt _ _ (MS _ ?Fx _ ?fcx _ ?mx _) => rename mx into m2; rename Fx into F2; rename fcx into fc2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
match goal with H : frm0 fc2 |- _ => rename H into FR2 end.
match goal with H : forall k : reg, _ -> reg_get F2 k = _ |- _ => rename H into HF2 end.
match goal with H : stk rsegs m2 _ _ |- _ => rename H into ST2 end.
match goal with H : rw_cells rsegs m2 (bv_unsigned sp + -111) _ |- _ => rename H into SB2 end.
match goal with H : ssp_cells m2 _ |- _ => rename H into SSP2 end.
clear SSP CAN1 CAN2 CAN3.
assert (FS2 : fsaved F F2).
{ eapply fsaved_trans; [exact FS|]. intros k Hk. apply HF2. cbn in Hk. pose proof Hk as Hk'.
intros E. repeat (destruct Hk' as [Hk'|Hk']; [subst k; cbv in E; discriminate E|]). exact Hk'. }
assert (SRC2 : bytes_at rsegs m2 Sa src).
{ eapply (src_presx _ _ _ m); [exact HP | exact (SRCk I) | exact MU |].
apply Forall_cons; [cbn; left; unfold_consts; lia|]. apply Forall_cons; [cbn; left; unfold_consts; lia|]. apply Forall_nil. }

assert (SB6 : bytes_at rsegs m2 (bv_unsigned sp + -111) (zb [92; 117; 48; 48; bv_unsigned h1; bv_unsigned h2])).
{ destruct SB2 as [[_ B] _]. cbn [cells_bytes cbytes app] in B.
destruct B as (B0 & B1 & B2). split; [lia|]. split; [cbn; lia|]. intros i Hi.
specialize (B2 i ltac:(cbn in Hi |- *; rewrite ?length_app, ?length_skipn in *; cbn in *; lia)).
cbn in Hi. do 6 (destruct i as [|i]; [exact B2|]). lia. }
destruct (Z.lt_ge_cases (cap - bpos) 7) as [SLOW|FAST].
-
symb_run 6%nat [0x2719c]%Z [false; false].
symb_run 12%nat [MEMAPPEND]%Z [true].
2: { sc_cbn. cbn [branch_taken]. rewrite room_test by lia. apply Z.ltb_lt. lia. }

assert (HP2 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m2 md) by (heap_now S4L HIx HP MU WM MI2).
assert (FR2c : rw_cells rsegs m2 (bv_unsigned sp + -144) (escF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j1 j2
(zb [92; 117; 48; 48; bv_unsigned h1; bv_unsigned h2] ++ Z_to_bv 8 0 :: skipn 7 sbf))).
{ unfold escF.
lazymatch goal with |- rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
change (rw_cells rsegs m2 A ([c1; c2; c3; c4; c5] ++ ([c6] ++ rest))) end.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRa|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 33) with 33.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [replace (bv_unsigned sp + -144 + 33) with (bv_unsigned sp + -111) by lia; exact SB2|].
cbn [cells_size csize Nat.add]. change (Z.of_nat 7) with 7. replace (bv_unsigned sp + -144 + 33 + 7) with (bv_unsigned sp + -104) by lia. exact FRd. }
assert (HPR2 : heap_pres S4L LB (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (INV2 : esc_memx m2 md).
{ exists A, buf, cap, bpos, content, errv, j1, j2. eexists.
split; [exact HP2|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF]|].
split; [exact FR2c|]. split; [exact SRC2|]. split; [exact ERR|]. split; [exact ST2|]. split; [exact HPR2 | exact VM]. }
apply evt_RZ_done.
eapply esc_appendx with (sb := zb [92; 117; 48; 48; bv_unsigned h1; bv_unsigned h2]);
[ exact INV2 | exact SB6 | reflexivity | lia | lia | lia | left; left; lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
pose proof INV' as INV1.
destruct INV' as (A' & buf' & cap' & bpos' & content' & errv' & j1' & j2' & sbf' & HP' & PB' & FRc' & SRC' & ERR' & ST' & HPR' & VM').
pose proof (heap_model_ok _ _ _ _ _ _ HP') as MOK'.
pose proof (heap_mem_inv _ _ _ _ _ _ HP') as MI'. cbn [hl_segs S4L] in MI'. unfold escF in FRc'.
apply rz_evt; [exact MOK'|].
symb_run 4%nat [0x27078]%Z (@nil bool).
apply evt_RZ_done; eapply esc_join98; try eassumption; lia.
-
symb_run 6%nat [0x2719c]%Z [false; false].
destruct (rw_cells_CB_cut rsegs _ _ _ _ (Z.to_nat bpos) PBUF ltac:(lia)) as [PB0 PB1].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 7%nat PB1 ltac:(lia)) as [PBD PB2]. clear PBUF PB1.
replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) in PBD, PB2 by lia.
replace (buf + bpos + Z.of_nat 7) with (buf + bpos + 7) in PB2 by lia.

rewrite (skipn_all2 sbf) in SB2 by lia.
apply (rw_cells_recast rsegs _ _ _ [C1 (Z_to_bv 8 92); C1 (Z_to_bv 8 117); C1 (Z_to_bv 8 48); C1 (Z_to_bv 8 48);
C1 (Z_to_bv 8 (bv_unsigned h1)); C1 (Z_to_bv 8 (bv_unsigned h2)); C1 (Z_to_bv 8 0)]) in SB2;
[| cbn; tauto | reflexivity | reflexivity].

apply (munch_weaken _ [(lo, bv_unsigned sp + -144); (bv_unsigned sp + -111, bv_unsigned sp + -104);
(buf + bpos, buf + bpos + 7)]) in MU;
[| unfold sub_fp; cbn [outside]; intros; lia].
pose proof (heap_blk_img S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as Himg. cbn [hl_img_lo hl_img_hi S4L] in Himg.
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as Hbimg. cbn [hl_img_lo hl_img_hi S4L] in Hbimg.
assert (SRCk2 : True -> bytes_at rsegs m2 Sa src) by (intros _; exact SRC2). clear SRC2.
pose proof (blk_ne_01 S4L HIx _ _ _ _ _ _ _ _ HP) as Hpbbuf.
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ pb PB_SZ buf cap HP ltac:(left; reflexivity) ltac:(right; left; reflexivity) Hpbbuf) as Hdisj.

symb_run 14%nat [0x271d0]%Z [false; false; false].
all: fast_sc.

symb_run 20%nat [0x2720c]%Z [false].
all: fast_sc.
apply (munch_weaken _ [(lo, bv_unsigned sp + -144); (bv_unsigned sp + -111, bv_unsigned sp + -104);
(buf + bpos, buf + bpos + 7); (pb + 8, pb + 12)]) in MU;
[| unfold sub_fp; cbn [outside]; intros; lia].

symb_run 16%nat [0x2723c]%Z [false; false; false].
all: fast_sc.

symb_run 4%nat [0x27074]%Z (@nil bool).

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
assert (HP3 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m3 md) by (heap_now S4L HIx HP MU WM MI3).

lazymatch type of PBD with rw_cells _ _ _ [C1 ?b0; C1 ?b1; C1 ?b2; C1 ?b3; C1 ?b4; C1 ?b5; C1 ?b6] =>
apply (rw_cells_recast rsegs _ _ _ [CB 7 [b0; b1; b2; b3; b4; b5; b6]]) in PBD; [| cbn; auto | reflexivity | reflexivity] end.
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ PB0 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos)) with (buf + bpos) by lia; exact PBD)) as J1.
pose proof (rw_cells_CB_join rsegs _ _ _ _ _ _ J1 ltac:(replace (buf + Z.of_nat (Z.to_nat bpos + 7)) with (buf + bpos + 7) by lia; exact PB2)) as J2.
replace (Z.to_nat bpos + 7 + (Z.to_nat cap - Z.to_nat bpos - 7))%nat with (Z.to_nat cap) in J2 by lia.
clear J1 PB0 PBD PB2.

lazymatch type of SB2 with rw_cells _ _ _ [C1 ?b0; C1 ?b1; C1 ?b2; C1 ?b3; C1 ?b4; C1 ?b5; C1 ?b6] =>
apply (rw_cells_recast rsegs _ _ _ [CB 7 [b0; b1; b2; b3; b4; b5; b6]]) in SB2; [| cbn; auto | reflexivity | reflexivity] end.
assert (FR3 : exists sb3, rw_cells rsegs m3 (bv_unsigned sp + -144) (escF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j1 j2 sb3)).
{ eexists. unfold escF.
lazymatch goal with |- rw_cells _ _ ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?rest) =>
change (rw_cells rsegs m3 A ([c1; c2; c3; c4; c5] ++ ([c6] ++ rest))) end.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRa|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 33) with 33.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [replace (bv_unsigned sp + -144 + 33) with (bv_unsigned sp + -111) by lia; exact SB2|].
cbn [cells_size csize Nat.add]. change (Z.of_nat 7) with 7. replace (bv_unsigned sp + -144 + 33 + 7) with (bv_unsigned sp + -104) by lia. exact FRd. }
destruct FR3 as [sb3 FR3].
assert (SRC3 : bytes_at rsegs m3 Sa src).
{ eapply (src_presx _ _ _ m); [exact HP | exact (SRCk I) | exact MU |].
apply Forall_cons; [cbn; left; unfold_consts; lia|]. apply Forall_cons; [cbn; left; unfold_consts; lia|].
apply Forall_cons; [cbn; right; left; lia|]. apply Forall_cons; [cbn; right; right; lia|]. apply Forall_nil. }
assert (HPR3 : heap_pres S4L LB (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }
assert (INV3 : esc_memx m3 md).
{ exists A, buf, cap, (bpos + 6). eexists. exists errv, j1, j2, sb3.
split; [exact HP3|]. split; [split; [lia|]; split; [lia|]; split; [| split; [exact PBS | exact J2]]|].
{ rewrite !length_app, length_firstn, !length_skipn. cbn [length]. lia. }
split; [exact FR3|]. split; [exact SRC3|]. split; [exact ERR|]. split; [exact ST2|]. split; [exact HPR3 | exact VM]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
symb_run 4%nat [0x27078]%Z (@nil bool).
apply evt_RZ_done; eapply esc_join98; try eassumption; lia.
Qed.

#[using="MEMMOVE HEXP usp SRCL SCL Hn HSa LO LOS SPA HT HT63 esc_appendx src_presx"] Lemma esc_ctrl_c10 :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m md pos start (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_cx 0x27118 x1 t0 t1 t2 (wz start) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (bv_unsigned c) F' fc' m pos) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos C32 CNS IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_c. prep INV HP FRc.
apply rz_evt; [exact MOK|].
destruct (Z.lt_ge_cases start pos) as [LT|GE].
- symb_run 8%nat [MEMAPPEND] [false; false].
try replace (start + Sa) with (Sa + start) by lia.
replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia.
replace (pos - start) with (Z.of_nat (Z.to_nat (pos - start))) by lia.
apply evt_RZ_done.
eapply esc_appendx with (sb := firstn (Z.to_nat (pos - start)) (skipn (Z.to_nat start) src));
[ exact INV0 | | | lia | lia | lia | | reflexivity | lia | reflexivity | exact FS | exact FR | ].
+ apply bytes_at_sub; [exact SRC | lia].
+ rewrite length_firstn, length_skipn. lia.
+ apply (src_cls_sub LB n usp Sa src); [exact SCL | exact SRCL | lia | lia].
+ intros m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_ctrl_tail; eassumption || lia.
- symb_run 8%nat [0x27130]%Z [true].
apply evt_RZ_done. eapply esc_ctrl_tail; eassumption || lia.
Qed.

#[using="MEMMOVE HEXP usp SRCL SCL Hn HSa LO LOS SPA HT HT63 esc_appendx src_presx"] Lemma esc_iter_ctrl :
forall x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m md pos start (c : byte) T,
esc_memx m md -> fsaved F F' -> frm0 fc' -> 0 <= start <= pos -> pos < n ->
nth_error src (Z.to_nat pos) = Some c ->
bv_unsigned c < 32 -> ~ In (bv_unsigned c) [8; 9; 10; 12; 13] ->
loopKx T (n - pos - 1) ->
(forall ms' md', esc_postx ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (st_loopx 0x27084 x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x27 t3 t4 t5 t6 F' fc' m pos pos start) md) T.
Proof.
intros until T. intros INV FS FR Hst Hpos Hc C32 CNS IH K.
pose proof INV as INV0.
destruct INV as (A & buf & cap & bpos & content & errv & j1 & j2 & sbf & HP & PB & FRc & SRC & ERR & ST & HPR & VM).
unfold st_loop. prep INV HP FRc.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
assert (SA0 : 0 < Sa) by (eapply (esc_sa_pos HIx); eassumption).
apply rz_evt; [exact MOK|].
symb_run 8%nat [0x2709c]%Z [false; false; false].
2: { sc_cbn. apply chk_nz_add; lia. }
assert (RG : 0 <= bv_unsigned c < 32) by lia.
symb_run 12%nat [0x27118]%Z [true] extra [Z_to_bv 64 (bv_unsigned c)].
apply evt_RZ_done. eapply esc_ctrl_c10; try eassumption; try lia.
sc_cbn. apply mask_clear_ctrl; assumption.
Qed.
End Esc.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7zy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7zy. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD4E.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD4E.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgLo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgLo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require US6h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import US6h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UM4C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UM4C. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgTW.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QId5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QId5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBGG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBGG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuoa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuoa.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULch.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULch.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition snpostI (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (o : list Z) (sb : list byte) (lo : Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength o)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, q); (D, D + 21)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ (frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo q
/\ rw_cells rsegs m' D [CB 21 (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) sb)]
/\ ssp_cells m' canary /\ 1 <= zlength o <= 20 /\ Forall (fun c => 45 <= c < 58) o).

#[using="Type"] Lemma dec_text_chars : forall i, Forall (fun c => 45 <= c < 58) (dec_text i).
Proof.
intros i. unfold dec_text. destruct (i <? 0).
- constructor; [lia|]. eapply Forall_impl; [| apply dec_digits_range]. intros c Hc. cbn in Hc. lia.
- destruct (i =? 0). { repeat constructor; lia. } eapply Forall_impl; [| apply dec_digits_range]. intros c Hc. cbn in Hc. lia.
Qed.

#[using="Type"] Lemma snprintf_ldZ :
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 : word) (D : Z) (v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sb : list byte) (lo : Z) (canary : word),
0 <= q < 2^63 -> 0 <= D -> D + 21 <= 2^64 -> length sb = 21%nat ->
rw_cells rsegs m D [CB 21 sb] -> stk rsegs m lo q -> lo <= q - SNPRINTF_DEPTH -> GLOBALS_TOP <= lo ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc -> (D + 21 <= lo \/ q <= D) -> GLOBALS_TOP <= D ->
evt rsegs (snpostI ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D (dec_text (bv_signed v)) sb lo canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 21) (Z_to_bv 64 A_FMT_ld) v a4
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Hq HD HD7 Lsb DST ST LOq GLO SSP MI FRM DD GD.
pose proof (bv_signed_in_range 64 v ltac:(lia)) as SR. unfold bv_half_modulus, bv_modulus in SR.
replace (2 ^ Z.of_N 64 `div` 2) with (2^63) in SR by reflexivity.
pose proof (bv_unsigned_in_range 64 v) as UR. unfold bv_modulus in UR. cbn in UR.
assert (HU : bv_unsigned v = bv_signed v mod 2^64).
{ unfold bv_signed, bv_swrap, bv_wrap.
replace (bv_half_modulus 64) with (2^63) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
Z.div_mod_to_equations. lia. }
pose proof (snprintf_ld_proof ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 21) (Z_to_bv 64 A_FMT_ld)
v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 21 (bv_signed v) 21%nat sb lo canary) as X.
cbv zeta in X. rewrite !unsigned_lit in X by lia.
pose proof (dec_text_length (bv_signed v) ltac:(lia)) as L.
eapply evt_mono; [eapply X; try reflexivity; try assumption; try lia |].
intros ms' P. unfold snprintf_post in P. unfold snpostI.
destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & E & MU & WM & MI' & FR' & HF & ST' & RW & SSP').
rewrite !unsigned_lit in MU, ST' by lia. change (Z.of_nat 21) with 21 in MU.
exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, Ft, fc', m'.
repeat (split; [assumption|]). apply dec_text_chars.
Qed.

#[using="Type"] Lemma snprintf_luZ :
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 : word) (D : Z) (v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sb : list byte) (lo : Z) (canary : word),
0 <= q < 2^63 -> 0 <= D -> D + 21 <= 2^64 -> length sb = 21%nat ->
rw_cells rsegs m D [CB 21 sb] -> stk rsegs m lo q -> lo <= q - SNPRINTF_DEPTH -> GLOBALS_TOP <= lo ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc -> (D + 21 <= lo \/ q <= D) -> GLOBALS_TOP <= D ->
evt rsegs (snpostI ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D (dec_text (bv_unsigned v)) sb lo canary m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 21) (Z_to_bv 64 A_FMT_lu) v a4
a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 snprintf_entry) fc None m (seg_rom rsegs)).
Proof.
intros until canary. intros Hq HD HD7 Lsb DST ST LOq GLO SSP MI FRM DD GD.
pose proof (bv_unsigned_in_range 64 v) as UR. unfold bv_modulus in UR. cbn in UR.
pose proof (snprintf_lu_proof ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 21) (Z_to_bv 64 A_FMT_lu)
v a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 21 (bv_unsigned v) 21%nat sb lo canary) as X.
cbv zeta in X. rewrite !unsigned_lit in X by lia.
pose proof (dec_text_length (bv_unsigned v) ltac:(lia)) as L.
eapply evt_mono; [eapply X; try reflexivity; try assumption; try lia |].
intros ms' P. unfold snprintf_post in P. unfold snpostI.
destruct P as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & E & MU & WM & MI' & FR' & HF & ST' & RW & SSP').
rewrite !unsigned_lit in MU, ST' by lia. change (Z.of_nat 21) with 21 in MU.
exists u0, u1, u2, v1, v2, v3, v4, v5, v6, v7, u3, u4, u5, u6, Ft, fc', m'.
repeat (split; [assumption|]). apply dec_text_chars.
Qed.

#[using="Type"] Lemma zb_nonul : forall o, Forall (fun c => 45 <= c < 58) o -> ~ In (Z_to_bv 8 0) (zb o).
Proof.
intros o H Hin. unfold zb in Hin. apply in_map_iff in Hin as (c & E & Hc).
pose proof (proj1 (Forall_forall _ _) H c Hc) as R. cbn in R.
apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
replace (bv_modulus 8) with 256 in E by reflexivity. rewrite !Z.mod_small in E by lia. lia.
Qed.
#[using="Type"] Lemma zb_length : forall o, length (zb o) = length o.
Proof. intros. unfold zb. apply length_map. Qed.

Section Ser.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis HT63 : hi_top S4L HIx < 2^63.

#[using="MEMMOVE HT63"] Lemma ser_int : ser_spec HIx SER_INT Sint.
Proof.
unfold ser_spec. intros until errv. intros HP PB JN INCL LBS FL Hlv Hlvd ST LO LOS SPA HT ERR TP' RA FRM A0 A1 A2 A3 K.
destruct JN as (cty & v & junk & EREST & Hcty & NODE). unfold jhdr_cells in NODE. cbn [app] in NODE.
subst a0 a1 a2 a3 tp. unfold TP, SER_INT, ERRNO in *. unfold ser_budget in LOS. cbn [sdepth Z.mul Z.add] in LOS.
word_range sp SPR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
assert (INp : In (p, 56) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; apply INCL; rewrite EREST; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ p 56 HP INp) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heap_blk S4L HIx _ _ _ _ pb PB_SZ HP ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP ltac:(right; left; reflexivity)) as (_ & Hbal & Hblo & Hbhi & _).
unfold_consts.
destruct FL as [Rfl FL56].
destruct PB as (Hbp & Hcap & Hlen & PBS & PBUF).
pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
carve_frame 48%nat ST.

assert (REST_OF : forall m1 (fmt : Z) (SNP : forall (ra0 : word) (q : Z) (gp0 tp0 t0_ t1_ t2_ s0_ s1_ : word) (D : Z)
(a4_ a5_ a6_ a7_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_ : word) (F0 : bvmap 5 word) (fc0 : bv 32) (mm : word -> option byte) (sb : list byte) (lo0 : Z) (canary : word),
0 <= q < 2^63 -> 0 <= D -> D + 21 <= 2^64 -> length sb = 21%nat ->
rw_cells rsegs mm D [CB 21 sb] -> stk rsegs mm lo0 q -> lo0 <= q - SNPRINTF_DEPTH -> GLOBALS_TOP <= lo0 ->
ssp_cells mm canary -> mem_inv rsegs mm -> frm0 fc0 -> (D + 21 <= lo0 \/ q <= D) -> GLOBALS_TOP <= D ->
evt rsegs (snpostI ra0 q gp0 tp0 s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ F0 D (dec_text (if fmt =? A_FMT_ld then bv_signed v else bv_unsigned v)) sb lo0 canary mm)
(MS (mkR ra0 (Z_to_bv 64 q) gp0 tp0 t0_ t1_ t2_ s0_ s1_ (Z_to_bv 64 D) (Z_to_bv 64 21) (Z_to_bv 64 fmt) v a4_
a5_ a6_ a7_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ s9_ s10_ s11_ t3_ t4_ t5_ t6_) F0 (Z_to_bv 64 snprintf_entry) fc0 None mm (seg_rom rsegs)))
(t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ : word) (j32 : list byte),
munch [(lo, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 32 j32; C8 s0; C8 ra] ->
rw_cells rsegs m1 pb [C8 (Z_to_bv 64 buf); C4 (Z_to_bv 64 bpos); C4 (Z_to_bv 64 cap)] ->
rw_cells rsegs m1 buf [CB (Z.to_nat cap) content] ->
rw_cells rsegs m1 490332 [C4 errv] ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 0x24a94) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 490496) t0_ t1_ t2_ (Z_to_bv 64 pb) s1
(Z_to_bv 64 (bv_unsigned sp + -37)) (Z_to_bv 64 21) (Z_to_bv 64 fmt) v a4_ a5_ a6_ a7_ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_ t4_ t5_ t6_)
F (Z_to_bv 64 snprintf_entry) fc None m1 (seg_rom rsegs))).
{ intros m1 fmt SNP t0_ t1_ t2_ a4_ a5_ a6_ a7_ t3_ t4_ t5_ t6_ j32 MU1 WM1 MI1 FR1 PBS1 PBUF1 ERR1 ST1.
clear MU WM FR ST PBS PBUF ERR NODE.
assert (HP1 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m1 md) by (heap_now S4L HIx HP MU1 WM1 MI1).
pose proof (heap_canary S4L HIx _ _ _ _ HP1) as (g & CAN1 & CAN2 & CAN3). cbn [hl_got_guard hl_guard hl_tp S4L] in CAN1, CAN2, CAN3.
pose proof (ssp_cells_of_bytes_at m1 g CAN1 CAN2) as SSP1. clear CAN1 CAN2 CAN3 HP1.

lazymatch type of FR1 with rw_cells _ _ ?A (?c1 :: ?rest) => change (rw_cells rsegs m1 A ([c1] ++ rest)) in FR1 end.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in FR1 as [FRab FRd]. cbn [cells_size csize Nat.add] in FRd. change (Z.of_nat 32) with 32 in FRd.
replace (bv_unsigned sp + -48 + 32) with (bv_unsigned sp + -16) in FRd by lia.
destruct (rw_cells_CB_cut rsegs _ _ _ _ 11%nat FRab ltac:(lia)) as [FRa FRb]. clear FRab.
replace (bv_unsigned sp + -48 + Z.of_nat 11) with (bv_unsigned sp + -37) in FRb by lia. change (32 - 11)%nat with 21%nat in FRb.
assert (LSB : length (skipn 11 j32) = 21%nat) by (destruct FRb as [[[W _] _] _]; cbn in W; lia).
set (o := dec_text (if fmt =? A_FMT_ld then bv_signed v else bv_unsigned v)) in SNP.
call (SNP _ (bv_unsigned sp + -48) _ _ _ _ _ _ _ (bv_unsigned sp + -37) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (skipn 11 j32) lo g);
[ first [ exact FRb | exact ST1 | exact SSP1 | exact MI1 | exact FRM | unfold SNPRINTF_DEPTH, GLOBALS_TOP in *; lia ] .. | ].
match goal with |- evt _ _ (MS _ ?Fx _ ?fcx _ ?mx _) => rename mx into m2; rename Fx into F2; rename fcx into fc2 end.
match goal with H : mem_inv rsegs m2 |- _ => rename H into MI2 end.
match goal with H : frm0 fc2 |- _ => rename H into FR2 end.
match goal with H : forall k : reg, _ -> reg_get F2 k = _ |- _ => rename H into HF2 end.
match goal with H : stk rsegs m2 _ _ |- _ => rename H into ST2 end.
match goal with H : rw_cells rsegs m2 (bv_unsigned sp + -37) _ |- _ => rename H into SB2 end.
match goal with H : Forall _ o |- _ => rename H into CH end.
match goal with H : 1 <= zlength o <= 20 |- _ => rename H into Lo end.
assert (FS2 : fsaved F F2).
{ intros k Hk. apply HF2. cbn in Hk. pose proof Hk as Hk'.
intros E. repeat (destruct Hk' as [Hk'|Hk']; [subst k; cbv in E; discriminate E|]). exact Hk'. }
clear HF2 SSP1.

unfold zlength in Lo.
assert (SBY : bytes_at rsegs m2 (bv_unsigned sp + -37) (zb o ++ Z_to_bv 8 0 :: (skipn (S (length o)) (skipn 11 j32) ++ (le8 s0 ++ le8 ra)))).
{ pose proof (rw_cells_bytes_at rsegs m2 _ _ SB2) as B1. cbn [cells_bytes cbytes app] in B1. rewrite app_nil_r in B1.
pose proof (rw_cells_bytes_at rsegs m2 _ _ FRd) as B2. cbn [cells_bytes cbytes] in B2. rewrite app_nil_r in B2.
destruct SB2 as [[[W _] _] _]. cbn in W. rewrite !length_app in W. cbn [length] in W.
replace (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) (skipn 11 j32) ++ le8 s0 ++ le8 ra)
with ((zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) (skipn 11 j32)) ++ (le8 s0 ++ le8 ra)) by (rewrite <- app_assoc; reflexivity).
apply (proj2 (bytes_at_app rsegs m2 _ _ _)). split; [exact B1|].
rewrite length_app. cbn [length]. replace (bv_unsigned sp + -37 + Z.of_nat (length (zb o) + S (length (skipn (S (length o)) (skipn 11 j32)))))
with (bv_unsigned sp + -16) by lia. exact B2. }
symb_run 3%nat [STRLEN] (@nil bool).
call (strlen_spec _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (bv_unsigned sp + -37)));
[ rewrite unsigned_lit by lia; exact SBY | apply zb_nonul; exact CH
| rewrite unsigned_lit by lia; rewrite !length_app, !length_skipn, zb_length; cbn [length]; rewrite !length_le8;
clear -Lo LSB SPA SPR; Z.div_mod_to_equations; lia
| exact MI2 | ].
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv rsegs m3 |- _ => rename H into MI3 end.
match goal with H : munch _ m m3 |- _ => rename H into MU3 end.
match goal with H : wmono rsegs m m3 |- _ => rename H into WM3 end.
match goal with H : stk rsegs m3 _ _ |- _ => rename H into ST3 end.
match goal with H : bytes_at rsegs m3 _ (zb o ++ _) |- _ => rename H into SBY3; rewrite unsigned_lit in SBY3 by lia end.
rewrite zb_length. assert (Lo31 : 0 <= Z.of_nat (length o) < 2^31) by lia.
symb_run 5%nat [MEMAPPEND] (@nil bool). rewrite ?Z.add_0_r.
assert (HP3 : HEAPx A ((pb, PB_SZ) :: (buf, cap) :: LB) m3 md) by (heap_now S4L HIx HP MU3 WM3 MI3).
assert (HPR3 : heap_pres S4L LB (bv_unsigned sp) m m3).
{ eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MU3 | exact WM3 |].
eapply (client_outside S4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | unfold_consts; lia |].
solve_clientW S4L HIx HP. }

match goal with H : rw_cells rsegs m3 (bv_unsigned sp + -48) _ |- _ => rename H into FRa3 end.
match goal with H : rw_cells rsegs m3 (bv_unsigned sp + -37) _ |- _ => rename H into FRb3 end.
match goal with H : rw_cells rsegs m3 (bv_unsigned sp + -16) _ |- _ => rename H into FRd3 end.
assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -48)
([CB 11 (firstn 11 j32)] ++ ([CB 21 (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) (skipn 11 j32))] ++ [C8 s0; C8 ra]))).
{ apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact FRa3|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 11) with 11.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [replace (bv_unsigned sp + -48 + 11) with (bv_unsigned sp + -37) by lia; exact FRb3|].
cbn [cells_size csize Nat.add]. change (Z.of_nat 21) with 21. replace (bv_unsigned sp + -48 + 11 + 21) with (bv_unsigned sp + -16) by lia. exact FRd3. }
cbn [app] in FR3.
assert (INV3 : ser_mem HIx sp m md LB pb lo (bv_unsigned sp + -48)
[CB 11 (firstn 11 j32); CB 21 (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) (skipn 11 j32)); C8 s0; C8 ra] m3 md).
{ exists A, buf, cap, bpos, content, errv.
split; [exact HP3|]. split; [split; [lia|]; split; [lia|]; split; [exact Hlen|]; split; [assumption|assumption]|].
split; [exact FR3|]. split; [assumption|]. split; [exact ST3|]. split; [exact HPR3 | apply model_vm_only_refl]. }
assert (SB3 : bytes_at rsegs m3 (bv_unsigned sp + -37) (zb o)) by (exact (proj1 (proj1 (bytes_at_app rsegs m3 _ _ _) SBY3))).
apply evt_RZ_done.
eapply (ser_append HIx MEMMOVE sp gp m md LB pb lo LO HT) with (F := F) (sb := zb o);
[ exact INV3 | exact SB3 | rewrite zb_length; lia | lia | lia | lia
| left; left; lia
| left; lia
| lia
| replace (bv_unsigned sp + -48) with (bv_unsigned sp - 16 * 3) by lia; rewrite <- Zminus_mod_idemp_l, SPA; reflexivity
| lia | lia | reflexivity | lia | reflexivity | exact FS2 | exact FR2 | ].
intros m4 md4 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F4 fc4 INV4 FS4 FR4 _.
destruct INV4 as (A4 & buf4 & cap4 & bpos4 & content4 & errv4 & HP4 & PB4 & FR4c & ERR4 & ST4 & HPR4 & VM4).
pose proof (heap_model_ok _ _ _ _ _ _ HP4) as MOK4.
pose proof (heap_mem_inv _ _ _ _ _ _ HP4) as MI4. cbn [hl_segs S4L] in MI4.
apply rz_evt; [exact MOK4|].
symb_run 8%nat (@nil Z) (@nil bool).
step.
apply evt_RZ_done. apply K. unfold ser_post.
exists m4, A4. eexists. exists errv4, buf4, cap4, bpos4, content4.
split; [| split; [exact VM4 | split; [| split; [exact HPR4 | split; [exact ERR4 | split; [exact HP4 | exact PB4]]]]]].
- replace (Z_to_bv 64 (bv_unsigned sp + -48 + 48)) with sp by (apply bv_eq; rewrite unsigned_lit by lia; lia).
apply ret_statew_intro; [exact FS4 | intros _; exact FR4].
- release_frame FR4c ST4 (bv_unsigned sp). exact ST4. }

destruct Hcty as [-> | ->].
- symb_run 22%nat [snprintf_entry] [false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
eapply (REST_OF _ A_FMT_ld); [ | eassumption .. ].
intros. change (A_FMT_ld =? A_FMT_ld) with true. cbv iota. eapply snprintf_ldZ; eassumption.
- symb_run 22%nat [snprintf_entry] [false; false].
2:{ sc_cbn. apply brne_and_zero; [lia | lia | apply land7_of_mod16; exact Hpal]. }
eapply (REST_OF _ A_FMT_lu); [ | eassumption .. ].
intros. change (A_FMT_lu =? A_FMT_ld) with false. cbv iota. eapply snprintf_luZ; eassumption.
Qed.
End Ser.

End RC__1.
