(* notice_seg_state_lib: the facts the N_STATE arm of notice's walk (notice_seg_state.v) uses: the record's region,
   shadow entry and facts, the branch tests, the record address, the stored values. *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGCg TransportGRwA TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import m_lost_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The pcs of the arm (listing offsets): the branch on GOT.n, the record path's stop before `addi a2, a4, 4`, the
   join (GOT.n + 1 stored back), the branch on n->state. *)
Definition NTS_BR1 : Z := AF_notice + 0xd4.
Definition NTS_REC : Z := AF_notice + 0xf8.
Definition NTS_JOIN : Z := AF_notice + 0x174.
Definition NTS_BR2 : Z := AF_notice + 0x194.

(* GOT's field GOT.n (base A_OBJ 13), the record GOT.t[GOT.n] (base atom 42, bytes 4 .. 16), their shadow entry, the
   facts with GOT's address and the record's range. *)
Definition nts_reg_gotn : YP09.region := nt_reg_fld 13 37.
Definition nts_SH2 : list shent := [mkSHE 11 0 72; mkSHE 42 4 16].
Definition nts_facts1 : facts := nt_facts_f (A_OBJ 13) TA_GOT.
Definition nts_facts2 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 (2 ^ 47 - 72) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (A_OBJ 13, mkAF TA_GOT TA_GOT 0);
           (42%nat, mkAF TA_GOT (TA_GOT + 180) 2)] [] [].

Lemma nts_facts2_ok : forall E sp p g,
  bv_unsigned (ew E 2) = sp -> bv_unsigned (ew E 11) = p -> ew E 32 = Z_to_bv 64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 -> sp mod 16 = 0 -> 4096 <= p <= 2 ^ 47 - 72 -> p mod 8 = 0 ->
  bv_unsigned (ew E (A_OBJ 13)) = TA_GOT -> bv_unsigned (ew E 42) = TA_GOT + 12 * g -> 0 <= g <= 15 ->
  facts_ok E nts_facts2.
Proof.
  intros E sp p g U2 U11 E32 Hsp Hsp16 Hp Hp8 U13 U42 Hg.
  unfold nts_facts2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U11, E32, U13, U42, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H4 : (TA_GOT + 12 * g) mod 4 = 0).
  { unfold TA_GOT. rewrite Z.add_mod by lia. rewrite Z.mul_mod by lia. reflexivity. }
  repeat match goal with |- _ /\ _ => split end; try exact I; first [exact H4 | unfold TA_GOT; lia | reflexivity].
Qed.

(* ---- values ---- *)

Lemma nts_lts : forall x y, -2^63 <= x < 2^63 -> -2^63 <= y < 2^63 -> bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !Z_to_bv_signed.
  rewrite !bv_swrap_small; [reflexivity | change (bv_half_modulus 64) with (2^63); lia
                            | change (bv_half_modulus 64) with (2^63); lia].
Qed.

Lemma nts_eqb : forall x y, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x mod 2^64 =? y mod 2^64).
Proof. intros. unfold bv_eqb. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* The branch at +0xd4: `blt a2, a7` with a2 = 15 and a7 the sign-extended GOT.n. *)
Lemma nts_br_got : forall E (Bw : list byte), ew E 37 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_n 4) ->
  branch_taken BC_LT (sv_denot E (SLit 15)) (sv_denot E (SExt true 32 (SOff 37 0))) = (15 <? TW.GOT_n Bw).
Proof.
  intros E Bw H37. pose proof (TWL.u_at_range Bw TW.A_GOT_n 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 37 _ H37 R). cbn [branch_taken sv_denot].
  change (bv_swrap 32 (TW.u_at Bw TW.A_GOT_n 4)) with (TW.GOT_n Bw).
  pose proof (nt_s32_range Bw TW.A_GOT_n) as Rg. change (TW.s32_at Bw TW.A_GOT_n) with (TW.GOT_n Bw) in Rg.
  apply nts_lts; lia.
Qed.

(* The branch at +0x194: `bne a0, a1` with a0 = the sign-extended n->state and a1 = 2. *)
Lemma nts_br_state : forall E (NB : list byte) s, ew E 34 = Z_to_bv 64 (TW.u_at NB 4 4) -> TW.s32_at NB 4 = s ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 34 0))) (sv_denot E (SLit 2)) = negb (s =? TC.S_ONLINE).
Proof.
  intros E NB s H34 Hs. pose proof (TWL.u_at_range NB 4 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  rewrite (nt_sext32 E 34 _ H34 R). cbn [branch_taken sv_denot].
  change (bv_swrap 32 (TW.u_at NB 4 4)) with (TW.s32_at NB 4). rewrite Hs.
  pose proof (nt_s32_range NB 4) as Rs. rewrite Hs in Rs.
  rewrite nts_eqb. unfold TC.S_ONLINE. f_equal.
  destruct (Z.eqb_spec s 2) as [->|Hn].
  - apply Z.eqb_eq. reflexivity.
  - apply Z.eqb_neq. intros Hm. apply Hn.
    destruct (Z_lt_le_dec s 0).
    + rewrite <- (Z.mod_add s 1 (2 ^ 64)) in Hm by lia. rewrite !Z.mod_small in Hm by lia. lia.
    + rewrite !Z.mod_small in Hm by lia. lia.
Qed.

(* The record's address at +0xf4: a4 = GOT + ((g << 4) - (g << 2)) = GOT + 12 g. *)
Lemma nts_rec_addr : forall E (Bw : list byte),
  ew E 37 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_n 4) -> bv_unsigned (ew E (A_OBJ 13)) = TA_GOT ->
  0 <= TW.GOT_n Bw <= 15 ->
  sv_denot E (SAlu ALU_ADD (SOff (A_OBJ 13) 0)
    (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 4))
       (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 2))))
  = Z_to_bv 64 (TA_GOT + 12 * TW.GOT_n Bw).
Proof.
  intros E Bw H37 U13 Hg. pose proof (TWL.u_at_range Bw TW.A_GOT_n 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  change (sv_denot E (SAlu ALU_ADD (SOff (A_OBJ 13) 0)
    (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 4))
       (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 2)))))
    with (alu64 ALU_ADD (sv_denot E (SOff (A_OBJ 13) 0))
      (alu64 ALU_SUB (alu64 ALU_SLL (sv_denot E (SExt true 32 (SOff 37 0))) (Z_to_bv 64 4))
         (alu64 ALU_SLL (sv_denot E (SExt true 32 (SOff 37 0))) (Z_to_bv 64 2)))).
  rewrite (nt_sext32 E 37 _ H37 R). change (bv_swrap 32 (TW.u_at Bw TW.A_GOT_n 4)) with (TW.GOT_n Bw).
  cbn [sv_denot]. rewrite U13, Z.add_0_r.
  cbn [alu64 alu]. apply bv_eq.
  rewrite ?bv_add_unsigned, ?bv_sub_unsigned, ?bv_shiftl_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  change (bv_unsigned (bv_and (Z_to_bv 64 4) (Z_to_bv 64 63))) with 4.
  change (bv_unsigned (bv_and (Z_to_bv 64 2) (Z_to_bv 64 63))) with 2.
  rewrite !(Z.mod_small (TW.GOT_n Bw)) by lia.
  rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
  rewrite (Z.mod_small (TW.GOT_n Bw * 16)) by lia. rewrite (Z.mod_small (TW.GOT_n Bw * 4)) by lia.
  rewrite (Z.mod_small (TW.GOT_n Bw * 16 - TW.GOT_n Bw * 4)) by lia.
  rewrite (Z.mod_small TA_GOT) by (unfold TA_GOT; lia).
  f_equal. lia.
Qed.

(* A sign-extended 4-byte value, stored by `sw`, read back as its low 32 bits: the u32 it was loaded as. *)
Lemma nts_sext_mod32 : forall u, 0 <= u < 2 ^ 32 ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 u)) mod 2 ^ 32 = u.
Proof.
  intros u Hu. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.mod_mod_divide by (exists (2 ^ 32); reflexivity).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31). rewrite Zminus_mod_idemp_l.
  replace (u + 2 ^ 31 - 2 ^ 31) with u by lia. apply Z.mod_small. exact Hu.
Qed.

Lemma nts_le_byte_swrap : forall u (j : nat), 0 <= u < 2 ^ 32 ->
  YO0f.le_byte u 4 j = YO0f.le_byte (bv_swrap 32 u) 4 j.
Proof.
  intros u j Hu. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. f_equal. f_equal.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32).
  change (2 ^ 32 / 2) with (2 ^ 31). rewrite Zminus_mod_idemp_l.
  replace (u + 2 ^ 31 - 2 ^ 31) with u by lia. reflexivity.
Qed.

Lemma nts_le_byte_small : forall v (m j : nat), 0 <= YO0f.le_byte v m j < 256.
Proof. intros v m j. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia. Qed.

Lemma nts_le_byte_mod32 : forall v (j : nat), YO0f.le_byte (v mod 2 ^ 32) 4 j = YO0f.le_byte v 4 j.
Proof.
  intros v j. unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma nts_mod_64_32 : forall v, bv_unsigned (Z_to_bv 64 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof.
  intros v. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity.
Qed.

(* ---- the record's shadow ---- *)

Section sh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.

(* GOT's payload is addressable at every AR state: its shadow is 0 (trans_notice_cells). *)
Lemma nts_got_ra : forall (B : asyms) ly S (W : world segs) mem md lo n,
  trans_notice_cells B -> @AR rc segs B ly S W mem md -> TA_GOT <= lo -> lo + n <= TA_GOT + TW.SZ_GOT ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF lo n.
Proof.
  intros B ly S W mem md lo n HZ HAR Hlo Hhi x Hx. unfold TW.SZ_GOT in Hhi.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (HT : TA_GOT mod 8 = 0) by (unfold TA_GOT; reflexivity).
  assert (Hz := decode_zshadow_rd B ly S W mem md TA_GOT (TA_GOT + TW.SZ_GOT) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TA_GOT in *; lia)
    ltac:(unfold TA_GOT, TW.SZ_GOT in *; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The run's shadow entries on the record path: the notice's 72 bytes and the record's 12. *)
Lemma nts_shok2 : forall (W : world segs) m (E : env) (g : Z),
  sh_ok segs NT_Bx NT_SH E (mrestrict (w_H W) m) ->
  range_addressable (aview segs (w_H W) m) SHADOW_OFF (TA_GOT + 12 * g + 4) 12 ->
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 42 = Z_to_bv 64 (TA_GOT + 12 * g) -> 0 <= g <= 15 ->
  sh_ok segs NT_Bx nts_SH2 E (mrestrict (w_H W) m).
Proof.
  intros W m E g SH1 HRA E32 E42 Hg.
  unfold sh_ok, NT_SH, nts_SH2 in *. inversion SH1 as [|e1 l1 H1 _]; subst.
  constructor; [exact H1|]. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) m E NT_Bx 42 (TA_GOT + 12 * g + 4) 12 (TA_GOT + 12 * g) 4 16 HRA).
  - unfold U, NT_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small.
    unfold TA_GOT. lia.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, TA_GOT in *. lia.
Qed.
End sh.
