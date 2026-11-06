(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec StepTac MuslStrlen CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

(* [comment removed for export] *)
Definition MEMCHR_WORDS : list (Z * Z) :=
  [(0x0, 0x0ff5f593); (0x4, 0x00757693); (0x8, 0x00c03733); (0xc, 0x02068c63); (0x10, 0x02060a63);
   (0x14, 0x00150793); (0x18, 0x00100813); (0x1c, 0x00054703); (0x20, 0x00060693); (0x24, 0x06b70e63);
   (0x28, 0x00150513); (0x2c, 0xfff68613); (0x30, 0x0077f893); (0x34, 0x00c03733); (0x38, 0x00088663);
   (0x3c, 0x00178793); (0x40, 0xfd069ee3); (0x44, 0x06070863); (0x48, 0x00054683); (0x4c, 0x04b68663);
   (0x50, 0x00800693); (0x54, 0x04d66263); (0x68, 0x00168793); (0x6c, 0x02f587b3); (0x70, 0x00700813);
   (0x74, 0x00053883); (0x78, 0x00f8c8b3); (0x7c, 0x411682b3); (0x80, 0x0112e8b3); (0x84, 0x00e8f8b3);
   (0x88, 0x02e89a63); (0x8c, 0xff860613); (0x90, 0x00850513); (0x94, 0xfec860e3); (0x98, 0x00060693);
   (0x9c, 0x00060c63); (0xa0, 0x00054603); (0xa4, 0x00b60a63); (0xa8, 0xfff68693); (0xac, 0x00150513);
   (0xb0, 0xfe0698e3); (0xb4, 0x00000513); (0xb8, 0x00008067); (0xbc, 0x00060693); (0xc0, 0x00054603);
   (0xc4, 0xfeb612e3); (0xc8, 0xff1ff06f)]%Z.

Lemma D_0 : decode_any (Z_to_bv 32 0x0ff5f593) = Some (OpImm ALU_AND 11 11 255, 4%Z). Proof. wdec. Qed.
Lemma D_4 : decode_any (Z_to_bv 32 0x00757693) = Some (OpImm ALU_AND 13 10 7, 4%Z). Proof. wdec. Qed.
Lemma D_8 : decode_any (Z_to_bv 32 0x00c03733) = Some (Op ALU_SLTU 14 0 12, 4%Z). Proof. wdec. Qed.
Lemma D_c : decode_any (Z_to_bv 32 0x02068c63) = Some (Branch BC_EQ 13 0 56, 4%Z). Proof. wdec. Qed.
Lemma D_10 : decode_any (Z_to_bv 32 0x02060a63) = Some (Branch BC_EQ 12 0 52, 4%Z). Proof. wdec. Qed.
Lemma D_14 : decode_any (Z_to_bv 32 0x00150793) = Some (OpImm ALU_ADD 15 10 1, 4%Z). Proof. wdec. Qed.
Lemma D_18 : decode_any (Z_to_bv 32 0x00100813) = Some (OpImm ALU_ADD 16 0 1, 4%Z). Proof. wdec. Qed.
Lemma D_1c : decode_any (Z_to_bv 32 0x00054703) = Some (Load SZ1 false 14 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_20 : decode_any (Z_to_bv 32 0x00060693) = Some (OpImm ALU_ADD 13 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_24 : decode_any (Z_to_bv 32 0x06b70e63) = Some (Branch BC_EQ 14 11 124, 4%Z). Proof. wdec. Qed.
Lemma D_28 : decode_any (Z_to_bv 32 0x00150513) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. wdec. Qed.
Lemma D_2c : decode_any (Z_to_bv 32 0xfff68613) = Some (OpImm ALU_ADD 12 13 4095, 4%Z). Proof. wdec. Qed.
Lemma D_30 : decode_any (Z_to_bv 32 0x0077f893) = Some (OpImm ALU_AND 17 15 7, 4%Z). Proof. wdec. Qed.
Lemma D_34 : decode_any (Z_to_bv 32 0x00c03733) = Some (Op ALU_SLTU 14 0 12, 4%Z). Proof. wdec. Qed.
Lemma D_38 : decode_any (Z_to_bv 32 0x00088663) = Some (Branch BC_EQ 17 0 12, 4%Z). Proof. wdec. Qed.
Lemma D_3c : decode_any (Z_to_bv 32 0x00178793) = Some (OpImm ALU_ADD 15 15 1, 4%Z). Proof. wdec. Qed.
Lemma D_40 : decode_any (Z_to_bv 32 0xfd069ee3) = Some (Branch BC_NE 13 16 8156, 4%Z). Proof. wdec. Qed.
Lemma D_44 : decode_any (Z_to_bv 32 0x06070863) = Some (Branch BC_EQ 14 0 112, 4%Z). Proof. wdec. Qed.
Lemma D_48 : decode_any (Z_to_bv 32 0x00054683) = Some (Load SZ1 false 13 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_4c : decode_any (Z_to_bv 32 0x04b68663) = Some (Branch BC_EQ 13 11 76, 4%Z). Proof. wdec. Qed.
Lemma D_50 : decode_any (Z_to_bv 32 0x00800693) = Some (OpImm ALU_ADD 13 0 8, 4%Z). Proof. wdec. Qed.
Lemma D_54 : decode_any (Z_to_bv 32 0x04d66263) = Some (Branch BC_LTU 12 13 68, 4%Z). Proof. wdec. Qed.
Lemma D_68 : decode_any (Z_to_bv 32 0x00168793) = Some (OpImm ALU_ADD 15 13 1, 4%Z). Proof. wdec. Qed.
Lemma D_6c : decode_any (Z_to_bv 32 0x02f587b3) = Some (Mul M_MUL 15 11 15, 4%Z). Proof. wdec. Qed.
Lemma D_70 : decode_any (Z_to_bv 32 0x00700813) = Some (OpImm ALU_ADD 16 0 7, 4%Z). Proof. wdec. Qed.
Lemma D_74 : decode_any (Z_to_bv 32 0x00053883) = Some (Load SZ8 true 17 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_78 : decode_any (Z_to_bv 32 0x00f8c8b3) = Some (Op ALU_XOR 17 17 15, 4%Z). Proof. wdec. Qed.
Lemma D_7c : decode_any (Z_to_bv 32 0x411682b3) = Some (Op ALU_SUB 5 13 17, 4%Z). Proof. wdec. Qed.
Lemma D_80 : decode_any (Z_to_bv 32 0x0112e8b3) = Some (Op ALU_OR 17 5 17, 4%Z). Proof. wdec. Qed.
Lemma D_84 : decode_any (Z_to_bv 32 0x00e8f8b3) = Some (Op ALU_AND 17 17 14, 4%Z). Proof. wdec. Qed.
Lemma D_88 : decode_any (Z_to_bv 32 0x02e89a63) = Some (Branch BC_NE 17 14 52, 4%Z). Proof. wdec. Qed.
Lemma D_8c : decode_any (Z_to_bv 32 0xff860613) = Some (OpImm ALU_ADD 12 12 4088, 4%Z). Proof. wdec. Qed.
Lemma D_90 : decode_any (Z_to_bv 32 0x00850513) = Some (OpImm ALU_ADD 10 10 8, 4%Z). Proof. wdec. Qed.
Lemma D_94 : decode_any (Z_to_bv 32 0xfec860e3) = Some (Branch BC_LTU 16 12 8160, 4%Z). Proof. wdec. Qed.
Lemma D_98 : decode_any (Z_to_bv 32 0x00060693) = Some (OpImm ALU_ADD 13 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_9c : decode_any (Z_to_bv 32 0x00060c63) = Some (Branch BC_EQ 12 0 24, 4%Z). Proof. wdec. Qed.
Lemma D_a0 : decode_any (Z_to_bv 32 0x00054603) = Some (Load SZ1 false 12 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_a4 : decode_any (Z_to_bv 32 0x00b60a63) = Some (Branch BC_EQ 12 11 20, 4%Z). Proof. wdec. Qed.
Lemma D_a8 : decode_any (Z_to_bv 32 0xfff68693) = Some (OpImm ALU_ADD 13 13 4095, 4%Z). Proof. wdec. Qed.
Lemma D_ac : decode_any (Z_to_bv 32 0x00150513) = Some (OpImm ALU_ADD 10 10 1, 4%Z). Proof. wdec. Qed.
Lemma D_b0 : decode_any (Z_to_bv 32 0xfe0698e3) = Some (Branch BC_NE 13 0 8176, 4%Z). Proof. wdec. Qed.
Lemma D_b4 : decode_any (Z_to_bv 32 0x00000513) = Some (OpImm ALU_ADD 10 0 0, 4%Z). Proof. wdec. Qed.
Lemma D_b8 : decode_any (Z_to_bv 32 0x00008067) = Some (Jalr 0 1 0, 4%Z). Proof. wdec. Qed.
Lemma D_bc : decode_any (Z_to_bv 32 0x00060693) = Some (OpImm ALU_ADD 13 12 0, 4%Z). Proof. wdec. Qed.
Lemma D_c0 : decode_any (Z_to_bv 32 0x00054603) = Some (Load SZ1 false 12 10 0, 4%Z). Proof. wdec. Qed.
Lemma D_c4 : decode_any (Z_to_bv 32 0xfeb612e3) = Some (Branch BC_NE 12 11 8164, 4%Z). Proof. wdec. Qed.
Lemma D_c8 : decode_any (Z_to_bv 32 0xff1ff06f) = Some (Jal 0 2097136, 4%Z). Proof. wdec. Qed.

(* [comment removed for export] *)
Definition const_ok (segs : list Segment) (c v : Z) : bool :=
  match rdn segs (fun _ => None) (Z_to_bv 64 c) 8 with
  | Some l => Z.eqb (bytes_le_to_Z l) v && Nat.eqb (length l) 8
  | None => false
  end.

(* [comment removed for export] *)
Definition MCLOB : list reg := [5; 10; 11; 12; 13; 14; 15; 16; 17].

Section Memchr.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Variables cM cH : Z.
Variables wam wlm wah wlh : Z.
Variables (iam iah : bv 20) (ilm ilh : bv 12).
Hypothesis HW : words_ok segs b MEMCHR_WORDS = true.
Hypothesis HFam : fetch_word segs (pcw b 0x58) = Some (Z_to_bv 32 wam).
Hypothesis HFlm : fetch_word segs (pcw b 0x5c) = Some (Z_to_bv 32 wlm).
Hypothesis HFah : fetch_word segs (pcw b 0x60) = Some (Z_to_bv 32 wah).
Hypothesis HFlh : fetch_word segs (pcw b 0x64) = Some (Z_to_bv 32 wlh).
Hypothesis HEam : is_ecall (Z_to_bv 32 wam) = false.
Hypothesis HElm : is_ecall (Z_to_bv 32 wlm) = false.
Hypothesis HEah : is_ecall (Z_to_bv 32 wah) = false.
Hypothesis HElh : is_ecall (Z_to_bv 32 wlh) = false.
Hypothesis HDam : decode_any (Z_to_bv 32 wam) = Some (Auipc 13 iam, 4%Z).
Hypothesis HDlm : decode_any (Z_to_bv 32 wlm) = Some (Load SZ8 true 13 13 ilm, 4%Z).
Hypothesis HDah : decode_any (Z_to_bv 32 wah) = Some (Auipc 14 iah, 4%Z).
Hypothesis HDlh : decode_any (Z_to_bv 32 wlh) = Some (Load SZ8 true 14 14 ilh, 4%Z).
Hypothesis HAM : pcw b (0x58 + bv_signed (bv_concat 32 iam (Z_to_bv 12 0))) + sext 64 ilm = Z_to_bv 64 cM.
Hypothesis HAH : pcw b (0x60 + bv_signed (bv_concat 32 iah (Z_to_bv 12 0))) + sext 64 ilh = Z_to_bv 64 cH.
Hypothesis HcM : const_ok segs cM Mc = true.
Hypothesis HcH : const_ok segs cH Hc = true.
Hypothesis Hcb : (0 <= cM /\ cM + 8 <= 2 ^ 64 /\ 0 <= cH /\ cH + 8 <= 2 ^ 64)%Z.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get segs b MEMCHR_WORDS); [exact HW | inw | lia].

Lemma F_0 : fetch_word segs (pcw b 0x0) = Some (Z_to_bv 32 0x0ff5f593). Proof. fw. Qed.
Lemma F_4 : fetch_word segs (pcw b 0x4) = Some (Z_to_bv 32 0x00757693). Proof. fw. Qed.
Lemma F_8 : fetch_word segs (pcw b 0x8) = Some (Z_to_bv 32 0x00c03733). Proof. fw. Qed.
Lemma F_c : fetch_word segs (pcw b 0xc) = Some (Z_to_bv 32 0x02068c63). Proof. fw. Qed.
Lemma F_10 : fetch_word segs (pcw b 0x10) = Some (Z_to_bv 32 0x02060a63). Proof. fw. Qed.
Lemma F_14 : fetch_word segs (pcw b 0x14) = Some (Z_to_bv 32 0x00150793). Proof. fw. Qed.
Lemma F_18 : fetch_word segs (pcw b 0x18) = Some (Z_to_bv 32 0x00100813). Proof. fw. Qed.
Lemma F_1c : fetch_word segs (pcw b 0x1c) = Some (Z_to_bv 32 0x00054703). Proof. fw. Qed.
Lemma F_20 : fetch_word segs (pcw b 0x20) = Some (Z_to_bv 32 0x00060693). Proof. fw. Qed.
Lemma F_24 : fetch_word segs (pcw b 0x24) = Some (Z_to_bv 32 0x06b70e63). Proof. fw. Qed.
Lemma F_28 : fetch_word segs (pcw b 0x28) = Some (Z_to_bv 32 0x00150513). Proof. fw. Qed.
Lemma F_2c : fetch_word segs (pcw b 0x2c) = Some (Z_to_bv 32 0xfff68613). Proof. fw. Qed.
Lemma F_30 : fetch_word segs (pcw b 0x30) = Some (Z_to_bv 32 0x0077f893). Proof. fw. Qed.
Lemma F_34 : fetch_word segs (pcw b 0x34) = Some (Z_to_bv 32 0x00c03733). Proof. fw. Qed.
Lemma F_38 : fetch_word segs (pcw b 0x38) = Some (Z_to_bv 32 0x00088663). Proof. fw. Qed.
Lemma F_3c : fetch_word segs (pcw b 0x3c) = Some (Z_to_bv 32 0x00178793). Proof. fw. Qed.
Lemma F_40 : fetch_word segs (pcw b 0x40) = Some (Z_to_bv 32 0xfd069ee3). Proof. fw. Qed.
Lemma F_44 : fetch_word segs (pcw b 0x44) = Some (Z_to_bv 32 0x06070863). Proof. fw. Qed.
Lemma F_48 : fetch_word segs (pcw b 0x48) = Some (Z_to_bv 32 0x00054683). Proof. fw. Qed.
Lemma F_4c : fetch_word segs (pcw b 0x4c) = Some (Z_to_bv 32 0x04b68663). Proof. fw. Qed.
Lemma F_50 : fetch_word segs (pcw b 0x50) = Some (Z_to_bv 32 0x00800693). Proof. fw. Qed.
Lemma F_54 : fetch_word segs (pcw b 0x54) = Some (Z_to_bv 32 0x04d66263). Proof. fw. Qed.
Lemma F_68 : fetch_word segs (pcw b 0x68) = Some (Z_to_bv 32 0x00168793). Proof. fw. Qed.
Lemma F_6c : fetch_word segs (pcw b 0x6c) = Some (Z_to_bv 32 0x02f587b3). Proof. fw. Qed.
Lemma F_70 : fetch_word segs (pcw b 0x70) = Some (Z_to_bv 32 0x00700813). Proof. fw. Qed.
Lemma F_74 : fetch_word segs (pcw b 0x74) = Some (Z_to_bv 32 0x00053883). Proof. fw. Qed.
Lemma F_78 : fetch_word segs (pcw b 0x78) = Some (Z_to_bv 32 0x00f8c8b3). Proof. fw. Qed.
Lemma F_7c : fetch_word segs (pcw b 0x7c) = Some (Z_to_bv 32 0x411682b3). Proof. fw. Qed.
Lemma F_80 : fetch_word segs (pcw b 0x80) = Some (Z_to_bv 32 0x0112e8b3). Proof. fw. Qed.
Lemma F_84 : fetch_word segs (pcw b 0x84) = Some (Z_to_bv 32 0x00e8f8b3). Proof. fw. Qed.
Lemma F_88 : fetch_word segs (pcw b 0x88) = Some (Z_to_bv 32 0x02e89a63). Proof. fw. Qed.
Lemma F_8c : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 0xff860613). Proof. fw. Qed.
Lemma F_90 : fetch_word segs (pcw b 0x90) = Some (Z_to_bv 32 0x00850513). Proof. fw. Qed.
Lemma F_94 : fetch_word segs (pcw b 0x94) = Some (Z_to_bv 32 0xfec860e3). Proof. fw. Qed.
Lemma F_98 : fetch_word segs (pcw b 0x98) = Some (Z_to_bv 32 0x00060693). Proof. fw. Qed.
Lemma F_9c : fetch_word segs (pcw b 0x9c) = Some (Z_to_bv 32 0x00060c63). Proof. fw. Qed.
Lemma F_a0 : fetch_word segs (pcw b 0xa0) = Some (Z_to_bv 32 0x00054603). Proof. fw. Qed.
Lemma F_a4 : fetch_word segs (pcw b 0xa4) = Some (Z_to_bv 32 0x00b60a63). Proof. fw. Qed.
Lemma F_a8 : fetch_word segs (pcw b 0xa8) = Some (Z_to_bv 32 0xfff68693). Proof. fw. Qed.
Lemma F_ac : fetch_word segs (pcw b 0xac) = Some (Z_to_bv 32 0x00150513). Proof. fw. Qed.
Lemma F_b0 : fetch_word segs (pcw b 0xb0) = Some (Z_to_bv 32 0xfe0698e3). Proof. fw. Qed.
Lemma F_b4 : fetch_word segs (pcw b 0xb4) = Some (Z_to_bv 32 0x00000513). Proof. fw. Qed.
Lemma F_b8 : fetch_word segs (pcw b 0xb8) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.
Lemma F_bc : fetch_word segs (pcw b 0xbc) = Some (Z_to_bv 32 0x00060693). Proof. fw. Qed.
Lemma F_c0 : fetch_word segs (pcw b 0xc0) = Some (Z_to_bv 32 0x00054603). Proof. fw. Qed.
Lemma F_c4 : fetch_word segs (pcw b 0xc4) = Some (Z_to_bv 32 0xfeb612e3). Proof. fw. Qed.
Lemma F_c8 : fetch_word segs (pcw b 0xc8) = Some (Z_to_bv 32 0xff1ff06f). Proof. fw. Qed.

(* [comment removed for export] *)
Lemma const_rd : forall mem c v, const_ok segs c v = true -> (0 <= c)%Z -> (c + 8 <= 2 ^ 64)%Z ->
  (forall x : word, (c <= bv_unsigned x < c + 8)%Z -> mem x = None) ->
  exists l, rdn segs mem (Z_to_bv 64 c) 8 = Some l /\ load_word SZ8 true l = Z_to_bv 64 v.
Proof.
  intros mem c v Hok Hc0 Hc8 Hro. unfold const_ok in Hok.
  rewrite (rdn_ext segs 8 mem (fun _ => None)).
  - destruct (rdn segs (fun _ => None) (Z_to_bv 64 c) 8) as [l|]; [|discriminate].
    apply andb_prop in Hok as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2.
    exists l. split; [reflexivity|]. apply bv_eq. rewrite u_ld8 by exact H2. rewrite H1.
    rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
    pose proof (bytes_le_to_Z_range l H2). lia.
  - rewrite bvu_z by lia. lia.
  - intros x Hx. rewrite bvu_z in Hx by lia. apply Hro. lia.
Qed.

Section Loop.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variables (s : word) (bs : list byte) (n : Z).
Local Notation L := (Z.of_nat (length bs)).
(* [comment removed for export] *)
Definition WE : Z := ((bv_unsigned s + L) / 8 * 8 + 8 - bv_unsigned s)%Z.
Hypothesis Hstr : cstr segs (ms_mem ms0) s bs.
Hypothesis Htail : forall j, (L < j < WE)%Z -> exists x, bat segs (ms_mem ms0) (s + Z_to_bv 64 j) = Some x.
Hypothesis Hnw : (bv_unsigned s + WE <= 2 ^ 64)%Z.
Hypothesis Hnl : no_lazy model (bv_unsigned s) (bv_unsigned s + WE).
Hypothesis Hn : (L + 8 <= n < 2 ^ 64)%Z.
Hypothesis HcellM : cell8 segs (ms_mem ms0) cM Mc.
Hypothesis HcellH : cell8 segs (ms_mem ms0) cH Hc.
Hypothesis HnlM : no_lazy model cM (cM + 8).
Hypothesis HnlH : no_lazy model cH (cH + 8).
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms', FR MCLOB ms0 ms' -> ms_pc_val ms' = rg ms0 1 -> rg ms' 10 = s + Z_to_bv 64 L ->
  realizes_cfg segs cfg (mkCfg ms' model) T.

(* [comment removed for export] *)
Definition B (j : Z) : byte := nth (Z.to_nat j) (bs ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma WE_facts : (L + 1 <= WE <= L + 8)%Z /\ ((bv_unsigned s + WE) mod 8 = 0)%Z.
Proof.
  unfold WE. pose proof (u64_range s).
  pose proof (Z.div_mod (bv_unsigned s + L) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned s + L) 8 ltac:(lia)).
  split; [lia|].
  replace (bv_unsigned s + ((bv_unsigned s + L) / 8 * 8 + 8 - bv_unsigned s))%Z
    with (1 * 8 + ((bv_unsigned s + L) / 8) * 8)%Z by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma B_nz : forall j, (0 <= j < L)%Z -> bv_unsigned (B j) <> 0%Z.
Proof.
  intros j Hj. unfold B. rewrite nth_app_l by lia. apply nul_free_nth; [exact (proj2 Hstr) | lia].
Qed.

Lemma B_z : bv_unsigned (B L) = 0%Z.
Proof. unfold B. rewrite Nat2Z.id, nth_app_last. reflexivity. Qed.

Lemma bat_B : forall j, (0 <= j <= L)%Z -> bat segs (ms_mem ms0) (s + Z_to_bv 64 j) = Some (B j).
Proof.
  intros j Hj. unfold B.
  pose proof (bat_of_rdn segs (ms_mem ms0) _ s _ (Z.to_nat j) (proj1 Hstr) ltac:(lia)) as H.
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

Lemma rd1 : forall j, (0 <= j <= L)%Z -> rdn segs (ms_mem ms0) (s + Z_to_bv 64 j) 1 = Some [B j].
Proof. intros j Hj. apply rdn_1. apply bat_B. exact Hj. Qed.

(* [comment removed for export] *)
Lemma al_room : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= L)%Z -> (j + 8 <= WE)%Z.
Proof.
  intros j Hal Hj. unfold WE. pose proof (u64_range s).
  pose proof (Z.div_mod (bv_unsigned s + L) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (bv_unsigned s + L) 8 ltac:(lia)).
  pose proof (Z.div_mod (bv_unsigned s + j) 8 ltac:(lia)).
  assert ((bv_unsigned s + j) / 8 <= (bv_unsigned s + L) / 8)%Z by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma u_sj : forall j, (0 <= j < WE)%Z -> bv_unsigned (s + Z_to_bv 64 j) = (bv_unsigned s + j)%Z.
Proof. intros j Hj. pose proof WE_facts. apply u_add_small; lia. Qed.

Lemma rd8 : forall j, ((bv_unsigned s + j) mod 8 = 0)%Z -> (0 <= j <= L)%Z ->
  exists l, rdn segs (ms_mem ms0) (s + Z_to_bv 64 j) 8 = Some l /\ length l = 8%nat /\
    (forall i, (i < 8)%nat -> (j + Z.of_nat i <= L)%Z -> nth i l (Z_to_bv 8 0) = B (j + Z.of_nat i)).
Proof.
  intros j Hal Hj. pose proof (al_room j Hal Hj) as HR.
  destruct (rdn_of_bats segs (ms_mem ms0) 8 (s + Z_to_bv 64 j)) as [l [Hl Hlen]].
  { intros i Hi. rewrite w_add_assoc.
    destruct (Z_le_gt_dec (j + Z.of_nat i) L) as [Hle|Hgt].
    - exists (B (j + Z.of_nat i)). apply bat_B. lia.
    - apply Htail. lia. }
  exists l. split; [exact Hl|]. split; [exact Hlen|].
  intros i Hi Hle. pose proof (bat_of_rdn segs (ms_mem ms0) 8 _ l i Hl Hi) as H1.
  rewrite w_add_assoc, bat_B in H1 by lia. injection H1 as <-. reflexivity.
Qed.

Lemma branch_eq_byte0 : forall x : byte,
  branch_taken BC_EQ (Z_to_bv 64 (bv_unsigned x)) w0 = (bv_unsigned x =? 0)%Z.
Proof. intros x. pose proof (byte_range x). unfold w0. apply branch_eq_z; lia. Qed.

Lemma branch_ne_byte0 : forall x : byte,
  branch_taken BC_NE (Z_to_bv 64 (bv_unsigned x)) w0 = negb (bv_unsigned x =? 0)%Z.
Proof. intros x. pose proof (byte_range x). unfold w0. apply branch_ne_z; lia. Qed.


Lemma rg1_keep : forall ms, FR MCLOB ms0 ms -> rg ms 1 = rg ms0 1.
Proof. intros ms (_ & _ & _ & _ & _ & _ & HR). apply HR. cbn. intuition discriminate. Qed.

(* [comment removed for export] *)
Lemma b_ret : forall ms, ms_pc_val ms = pcw b 0xb8 -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 L ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms Hpc HF H10. pose proof HF as (Hsvc & _).
  eapply rzc_acc; [ assumption | exact Hsvc | eapply wacc_Jalr; [ fetch_tac F_b8 | reflexivity | exact D_b8 ] | apply acc_ok_nil | ].
  rgn. rewrite ?pc_setx. rewrite (rg1_keep ms HF), ret_even by exact Hra.
  apply HK; [ frs HF | reflexivity | rgn; exact H10 ].
Qed.

(* [comment removed for export] *)
Ltac wlb F D H10 Hmem :=
  eapply rzc_acc;
  [ assumption | first [ reflexivity | assumption ]
  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | rgn; rewrite ?H10, add_sext0, ?mem_setx, ?Hmem; apply rd1; lia ]
  | apply acc_ok_one; rgn; rewrite ?H10, add_sext0; cbn [msz_n]; rewrite u_sj by (pose proof WE_facts; lia);
    [ lia | apply (no_lazy_sub model _ _ _ _ Hnl); pose proof WE_facts; lia ]
  | try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn; rewrite lbu_val; nrm ].

(* [comment removed for export] *)
Lemma t_loop : forall d j m ms, (j + Z.of_nat d = L)%Z -> (0 <= j)%Z ->
  ms_pc_val ms = pcw b 0xa0 -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 13 = Z_to_bv 64 m -> (L - j + 1 <= m < 2 ^ 64)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros j m ms Hjd Hj0 Hpc HF H10 H11 H13 Hm;
    pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _); pose proof WE_facts as HWE.
  - assert (Hj : j = L) by lia. subst j.
    wlb F_a0 D_a0 H10 Hmem.
    wsx wacc_Branch F_a4 D_a4. rgn. rewrite H11, branch_eq_byte0, B_z. cbn [Z.eqb]. pcn.
    apply b_ret; [ reflexivity | frs HF | rgn; exact H10 ].
  - wlb F_a0 D_a0 H10 Hmem.
    wsx wacc_Branch F_a4 D_a4. rgn. rewrite H11, branch_eq_byte0.
    rewrite (proj2 (Z.eqb_neq _ 0%Z) (B_nz j ltac:(lia))). pcn.
    wsx wacc_OpImm F_a8 D_a8. rgn. rewrite H13, alu_add, zw_add_sext. lits.
    wsx wacc_OpImm F_ac D_ac. rgn. rewrite H10, alu_add, w_add_sext_z. lits.
    wsx wacc_Branch F_b0 D_b0. rgn. unfold w0. rewrite branch_ne_z by lia.
    rewrite (proj2 (Z.eqb_neq (m + -1) 0%Z)) by lia. cbn [negb]. pcn.
    apply (IH (j + 1)%Z (m + -1)%Z); [ lia | lia | reflexivity | frs HF | rgn; reflexivity | rgn; exact H11 | rgn; reflexivity | lia ].
Qed.

(* [comment removed for export] *)
Lemma tail_a8 : forall j m ms, (0 <= j < L)%Z ->
  ms_pc_val ms = pcw b 0xa8 -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 13 = Z_to_bv 64 m -> (L - j + 1 <= m < 2 ^ 64)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros j m ms Hj Hpc HF H10 H11 H13 Hm. pose proof HF as (Hsvc & _).
  wsx wacc_OpImm F_a8 D_a8. rgn. rewrite H13, alu_add, zw_add_sext. lits.
  wsx wacc_OpImm F_ac D_ac. rgn. rewrite H10, alu_add, w_add_sext_z. lits.
  wsx wacc_Branch F_b0 D_b0. rgn. unfold w0. rewrite branch_ne_z by lia.
  rewrite (proj2 (Z.eqb_neq (m + -1) 0%Z)) by lia. cbn [negb]. pcn.
  apply (t_loop (Z.to_nat (L - (j + 1))) (j + 1)%Z (m + -1)%Z);
    [ lia | lia | reflexivity | frs HF | rgn; reflexivity | rgn; exact H11 | rgn; reflexivity | lia ].
Qed.

(* [comment removed for export] *)
Lemma wf_block : forall j m ms, (0 <= j <= L)%Z ->
  ms_pc_val ms = pcw b 0xbc -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 m -> (L - j + 1 <= m < 2 ^ 64)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros j m ms Hj Hpc HF H10 H11 H12 Hm. pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _). pose proof WE_facts as HWE.
  wsx wacc_OpImm F_bc D_bc. rgn. rewrite H12, alu_add, add_sext0.
  wlb F_c0 D_c0 H10 Hmem.
  wsx wacc_Branch F_c4 D_c4. rgn. rewrite H11, branch_ne_byte0.
  destruct (Z.eq_dec j L) as [->|Hne].
  - rewrite B_z. cbn [Z.eqb negb]. pcn.
    wsx wacc_Jal F_c8 D_c8. lits.
    apply b_ret; [ reflexivity | frs HF | rgn; exact H10 ].
  - rewrite (proj2 (Z.eqb_neq _ 0%Z) (B_nz j ltac:(lia))). cbn [negb]. pcn.
    apply (tail_a8 j m); [ lia | reflexivity | frs HF | rgn; exact H10 | rgn; exact H11 | rgn; reflexivity | lia ].
Qed.

(* [comment removed for export] *)
Lemma w_loop : forall d j m ms, (Z.of_nat d = (L - j) / 8)%Z -> (0 <= j <= L)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z ->
  ms_pc_val ms = pcw b 0x74 -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 m -> rg ms 13 = Z_to_bv 64 Mc -> rg ms 14 = Z_to_bv 64 Hc -> rg ms 15 = w0 ->
  rg ms 16 = Z_to_bv 64 7 -> (L - j + 8 <= m < 2 ^ 64)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros j m ms Hd Hj Hal Hpc HF H10 H11 H12 H13 H14 H15 H16 Hm;
    pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _); pose proof WE_facts as HWE;
    pose proof (al_room j Hal Hj) as HR;
    destruct (rd8 j Hal Hj) as (l & Hl & Hlen & Hnth).
  all: eapply rzc_acc; [ assumption | assumption
       | eapply wacc_Load; [ fetch_tac F_74 | reflexivity | exact D_74 | rewrite H10, add_sext0, Hmem; exact Hl ]
       | apply acc_ok_one; rewrite H10, add_sext0; cbn [msz_n]; rewrite u_sj by lia;
         [ lia | apply (no_lazy_sub model _ _ _ _ Hnl); lia ]
       | rewrite Hpc; pcn ].
  all: wsx wacc_Op F_78 D_78. all: rgn. all: rewrite H15.
  all: wsx wacc_Op F_7c D_7c. all: rgn. all: rewrite H13.
  all: wsx wacc_Op F_80 D_80. all: rgn.
  all: wsx wacc_Op F_84 D_84. all: rgn. all: rewrite H14.
  all: wsx wacc_Branch F_88 D_88. all: rgn. all: rewrite ?H14.
  all: fold (TWr (load_word SZ8 true l)).
  - (* [comment removed for export] *)
    assert (HKj : (L < j + 8)%Z) by (pose proof (Z.div_mod (L - j) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (L - j) 8 ltac:(lia)); lia).
    rewrite (TWr_haszero l (Z.to_nat (L - j)) Hlen ltac:(lia)).
    + pcn. apply (wf_block j m); [lia | reflexivity | frs HF | rgn; exact H10 | rgn; exact H11 | rgn; exact H12 | lia].
    + rewrite Hnth by lia. rewrite Z2Nat.id by lia. replace (j + (L - j))%Z with L by lia. exact B_z.
    + intros i Hi. rewrite Hnth by lia. apply B_nz. lia.
  - (* [comment removed for export] *)
    assert (HKj : (j + 8 <= L)%Z) by (pose proof (Z.div_mod (L - j) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (L - j) 8 ltac:(lia)); lia).
    rewrite (TWr_nozero l Hlen).
    2:{ intros i Hi. rewrite Hnth by lia. apply B_nz. lia. }
    pcn.
    wsx wacc_OpImm F_8c D_8c. rgn. rewrite H12, alu_add, zw_add_sext. lits.
    wsx wacc_OpImm F_90 D_90. rgn. rewrite H10, alu_add, w_add_sext_z. lits.
    wsx wacc_Branch F_94 D_94. rgn. rewrite H16. rewrite branch_ltu_z by lia.
    rewrite (proj2 (Z.ltb_lt 7 (m + -8))) by lia. pcn.
    apply (IH (j + 8)%Z (m + -8)%Z).
    + assert (E : (L - (j + 8) = (L - j) + -1 * 8)%Z) by lia. rewrite E, Z.div_add by lia. lia.
    + lia.
    + replace (bv_unsigned s + (j + 8))%Z with (bv_unsigned s + j + 1 * 8)%Z by lia. rewrite Z.mod_add by lia. exact Hal.
    + reflexivity.
    + frs HF.
    + rgn. reflexivity.
    + rgn. exact H11.
    + rgn. reflexivity.
    + rgn. exact H13.
    + rgn. exact H14.
    + rgn. exact H15.
    + rgn. exact H16.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma w_block : forall j m ms, (0 <= j <= L)%Z -> ((bv_unsigned s + j) mod 8 = 0)%Z ->
  ms_pc_val ms = pcw b 0x44 -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 m -> rg ms 14 = Z_to_bv 64 1 -> (L - j + 8 <= m < 2 ^ 64)%Z ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros j m ms Hj Hal Hpc HF H10 H11 H12 H14 Hm.
  pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _). pose proof WE_facts as HWE.
  wsx wacc_Branch F_44 D_44. rgn. rewrite H14, (br_eq0 1) by lia. cbn [Z.eqb]. pcn.
  wlb F_48 D_48 H10 Hmem.
  wsx wacc_Branch F_4c D_4c. rgn. rewrite H11, branch_eq_byte0.
  destruct (Z.eq_dec j L) as [->|Hne].
  - rewrite B_z. cbn [Z.eqb]. pcn.
    wsx wacc_OpImm F_98 D_98. rgn. rewrite H12, alu_add, add_sext0.
    wsx wacc_Branch F_9c D_9c. rgn. rewrite ?H12, (br_eq0 m) by lia.
    rewrite (proj2 (Z.eqb_neq m 0%Z)) by lia. pcn.
    apply (t_loop 0 L m); [ lia | lia | reflexivity | frs HF | rgn; exact H10 | rgn; exact H11 | rgn; reflexivity | lia ].
  - rewrite (proj2 (Z.eqb_neq _ 0%Z) (B_nz j ltac:(lia))). pcn.
    wsx wacc_OpImm F_50 D_50. rgn. rewrite alu_add, w0_add_sext. lits.
    wsx wacc_Branch F_54 D_54. rgn. rewrite H12. rewrite branch_ltu_z by lia.
    rewrite (proj2 (Z.ltb_ge m 8)) by lia. pcn.
    (* [comment removed for export] *)
    eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Auipc; [ fetch_tac HFam | exact HEam | exact HDam ] | apply acc_ok_nil | ].
    pcn; nrm.
    destruct HcellM as (lM & HlM & HvM).
    eapply rzc_acc; [ assumption | reflexivity
      | eapply wacc_Load; [ fetch_tac HFlm | exact HElm | exact HDlm | rgn; rewrite ?pc_setx, HAM, ?mem_setx, Hmem; exact HlM ]
      | apply acc_ok_one; rgn; rewrite ?pc_setx, HAM; cbn [msz_n]; rewrite bvu_z by lia; [ lia | exact HnlM ]
      | ].
    pcn; nrm. rewrite HvM.
    (* [comment removed for export] *)
    eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Auipc; [ fetch_tac HFah | exact HEah | exact HDah ] | apply acc_ok_nil | ].
    pcn; nrm.
    destruct HcellH as (lH & HlH & HvH).
    eapply rzc_acc; [ assumption | reflexivity
      | eapply wacc_Load; [ fetch_tac HFlh | exact HElh | exact HDlh | rgn; rewrite ?pc_setx, HAH, ?mem_setx, Hmem; exact HlH ]
      | apply acc_ok_one; rgn; rewrite ?pc_setx, HAH; cbn [msz_n]; rewrite bvu_z by lia; [ lia | exact HnlH ]
      | ].
    pcn; nrm. rewrite HvH.
    wsx wacc_OpImm F_68 D_68. rgn.
    eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Mul; [ fetch_tac F_6c | reflexivity | exact D_6c ] | apply acc_ok_nil | ].
    pcn; nrm. rgn. rewrite H11, mul_w0.
    wsx wacc_OpImm F_70 D_70. rgn. rewrite ?alu_add, w0_add_sext. lits.
    apply (w_loop (Z.to_nat ((L - j) / 8)) j m).
    + rewrite Z2Nat.id; [reflexivity|]. apply Z.div_pos; lia.
    + lia.
    + exact Hal.
    + reflexivity.
    + frs HF.
    + rgn. exact H10.
    + rgn. exact H11.
    + rgn. exact H12.
    + rgn. reflexivity.
    + rgn. reflexivity.
    + rgn. reflexivity.
    + rgn. reflexivity.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma h_loop : forall d j ms, (Z.of_nat d + (bv_unsigned s + j) mod 8 = 7)%Z -> (0 <= j <= L)%Z ->
  ms_pc_val ms = pcw b 0x1c -> FR MCLOB ms0 ms -> rg ms 10 = s + Z_to_bv 64 j -> rg ms 11 = w0 ->
  rg ms 12 = Z_to_bv 64 (n - j) -> rg ms 15 = s + Z_to_bv 64 (j + 1) -> rg ms 16 = Z_to_bv 64 1 ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  induction d as [|d IH]; intros j ms Hd Hj Hpc HF H10 H11 H12 H15 H16;
    pose proof HF as (Hsvc & _ & _ & _ & _ & Hmem & _); pose proof WE_facts as HWE.
  all: wlb F_1c D_1c H10 Hmem.
  all: wsx wacc_OpImm F_20 D_20. all: rgn. all: rewrite H12, alu_add, add_sext0.
  all: wsx wacc_Branch F_24 D_24. all: rgn. all: rewrite H11, branch_eq_byte0.
  all: destruct (Z.eq_dec j L) as [->|Hne].
  1,3: rewrite B_z; cbn [Z.eqb]; pcn;
       apply (t_loop 0 L (n - L)); [ lia | lia | reflexivity | frs HF | rgn; exact H10 | rgn; exact H11 | rgn; reflexivity | lia ].
  all: rewrite (proj2 (Z.eqb_neq _ 0%Z) (B_nz j ltac:(lia))); pcn.
  all: wsx wacc_OpImm F_28 D_28. all: rgn. all: rewrite H10, alu_add, w_add_sext_z. all: lits.
  all: wsx wacc_OpImm F_2c D_2c. all: rgn. all: rewrite alu_add, zw_add_sext. all: lits.
  all: wsx wacc_OpImm F_30 D_30. all: rgn. all: rewrite H15, and7, u_sj by lia.
  all: wsx wacc_Op F_34 D_34. all: rgn. all: rewrite sltu0 by lia.
  all: wsx wacc_Branch F_38 D_38. all: rgn.
  all: rewrite (br_eq0 ((bv_unsigned s + (j + 1)) mod 8)) by (pose proof (Z.mod_pos_bound (bv_unsigned s + (j + 1)) 8 ltac:(lia)); lia).
  - (* [comment removed for export] *)
    assert (Ha : ((bv_unsigned s + (j + 1)) mod 8 = 0)%Z).
    { replace (bv_unsigned s + (j + 1))%Z with ((bv_unsigned s + j) + 1)%Z by lia.
      rewrite Z.add_mod by lia. replace ((bv_unsigned s + j) mod 8)%Z with 7%Z by lia. reflexivity. }
    rewrite Ha. cbn [Z.eqb]. pcn.
    apply (w_block (j + 1) (n - j + -1)); [ lia | exact Ha | reflexivity | frs HF | rgn; reflexivity | rgn; exact H11
      | rgn; reflexivity | rgn; reflexivity | lia ].
  - (* [comment removed for export] *)
    assert (Ha : ((bv_unsigned s + (j + 1)) mod 8 = (bv_unsigned s + j) mod 8 + 1)%Z).
    { replace (bv_unsigned s + (j + 1))%Z with ((bv_unsigned s + j) + 1)%Z by lia.
      rewrite Z.add_mod by lia. rewrite (Z.mod_small 1) by lia.
      rewrite Z.mod_small; [reflexivity|]. pose proof (Z.mod_pos_bound (bv_unsigned s + j) 8 ltac:(lia)). lia. }
    rewrite (proj2 (Z.eqb_neq _ 0%Z)) by lia. pcn.
    wsx wacc_OpImm F_3c D_3c. rgn. rewrite H15, alu_add, w_add_sext_z. lits.
    wsx wacc_Branch F_40 D_40. rgn. rewrite ?H12, H16. rewrite branch_ne_z by lia.
    rewrite (proj2 (Z.eqb_neq (n - j) 1%Z)) by lia. cbn [negb]. pcn.
    apply (IH (j + 1)%Z); [ lia | lia | reflexivity | frs HF | rgn; reflexivity | rgn; exact H11
      | rgn; f_equal; lia | rgn; f_equal; lia | rgn; exact H16 ].
Qed.

(* [comment removed for export] *)
Lemma memchr_entry : ms_svc_pending ms0 = None -> ms_pc_val ms0 = pcw b 0 ->
  rg ms0 10 = s -> rg ms0 11 = w0 -> rg ms0 12 = Z_to_bv 64 n ->
  realizes_cfg segs cfg (mkCfg ms0 model) T.
Proof.
  intros Hsvc Hpc H10 H11 H12. pose proof WE_facts as HWE.
  assert (HF : FR MCLOB ms0 ms0) by (apply FR_refl; exact Hsvc).
  pose proof (u64_range s) as Hs.
  pose proof (Z.mod_pos_bound (bv_unsigned s) 8 ltac:(lia)) as Hsm.
  wsx wacc_OpImm F_0 D_0. rgn. rewrite H11, and_w0.
  wsx wacc_OpImm F_4 D_4. rgn. rewrite H10, and7.
  wsx wacc_Op F_8 D_8. rgn. rewrite H12, sltu0 by lia.
  wsx wacc_Branch F_c D_c. rgn. rewrite (br_eq0 (bv_unsigned s mod 8)) by lia.
  destruct (Z.eq_dec (bv_unsigned s mod 8) 0) as [Ha|Ha].
  - rewrite Ha. cbn [Z.eqb]. pcn.
    apply (w_block 0 n); [ lia | rewrite Z.add_0_r; exact Ha | reflexivity | frs HF | rgn; rewrite H10, w_add_0; reflexivity
      | rgn; reflexivity | rgn; exact H12 | rgn; reflexivity | lia ].
  - rewrite (proj2 (Z.eqb_neq _ 0%Z) Ha). pcn.
    wsx wacc_Branch F_10 D_10. rgn. rewrite H12, (br_eq0 n) by lia. rewrite (proj2 (Z.eqb_neq n 0%Z)) by lia. pcn.
    wsx wacc_OpImm F_14 D_14. rgn. rewrite H10, alu_add, w_add_sext. lits.
    wsx wacc_OpImm F_18 D_18. rgn. rewrite ?alu_add, w0_add_sext. lits.
    apply (h_loop (Z.to_nat (7 - bv_unsigned s mod 8)) 0).
    + rewrite Z2Nat.id by lia. rewrite Z.add_0_r. lia.
    + lia.
    + reflexivity.
    + frs HF.
    + rgn. rewrite H10, w_add_0. reflexivity.
    + rgn. reflexivity.
    + rgn. rewrite H12. f_equal. lia.
    + rgn. reflexivity.
    + rgn. reflexivity.
Qed.

End Loop.

(* [comment removed for export] *)
Theorem memchr_sum : forall (ms : machine_state) (model : Model) (T : TSet) (s : word) (bs : list byte) (n : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10 = s -> rg ms 11 = w0 -> rg ms 12 = Z_to_bv 64 n ->
  cstr segs (ms_mem ms) s bs ->
  (forall j, (Z.of_nat (length bs) < j < WE s bs)%Z -> exists x, bat segs (ms_mem ms) (s + Z_to_bv 64 j) = Some x) ->
  (bv_unsigned s + WE s bs <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + WE s bs) ->
  (Z.of_nat (length bs) + 8 <= n < 2 ^ 64)%Z ->
  cell8 segs (ms_mem ms) cM Mc -> cell8 segs (ms_mem ms) cH Hc ->
  no_lazy model cM (cM + 8) -> no_lazy model cH (cH + 8) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', FR MCLOB ms ms' -> ms_pc_val ms' = rg ms 1 -> rg ms' 10 = s + Z_to_bv 64 (Z.of_nat (length bs)) ->
     realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model T s bs n Hsvc Hpc Hh H10 H11 H12 Hstr Htail Hnw Hnl Hn HcellM HcellH HnlM HnlH Hra HK.
  exact (memchr_entry model Hh ms T s bs n Hstr Htail Hnw Hnl Hn HcellM HcellH HnlM HnlH Hra HK Hsvc Hpc H10 H11 H12).
Qed.

(* [comment removed for export] *)
Corollary memchr_sum_ro : forall (ms : machine_state) (model : Model) (T : TSet) (s : word) (bs : list byte) (n : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10 = s -> rg ms 11 = w0 -> rg ms 12 = Z_to_bv 64 n ->
  cstr segs (ms_mem ms) s bs ->
  (forall j, (Z.of_nat (length bs) < j < WE s bs)%Z -> exists x, bat segs (ms_mem ms) (s + Z_to_bv 64 j) = Some x) ->
  (bv_unsigned s + WE s bs <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + WE s bs) ->
  (Z.of_nat (length bs) + 8 <= n < 2 ^ 64)%Z ->
  (forall x : word, (cM <= bv_unsigned x < cM + 8 \/ cH <= bv_unsigned x < cH + 8)%Z -> ms_mem ms x = None) ->
  no_lazy model cM (cM + 8) -> no_lazy model cH (cH + 8) ->
  (bv_unsigned (rg ms 1) mod 2 = 0)%Z ->
  (forall ms', FR MCLOB ms ms' -> ms_pc_val ms' = rg ms 1 -> rg ms' 10 = s + Z_to_bv 64 (Z.of_nat (length bs)) ->
     realizes_cfg segs cfg (mkCfg ms' model) T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model T s bs n Hsvc Hpc Hh H10 H11 H12 Hstr Htail Hnw Hnl Hn Hro HnlM HnlH Hra HK.
  apply (memchr_sum ms model T s bs n); try assumption.
  - exact (const_rd (ms_mem ms) cM Mc HcM ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hro; left; exact Hx)).
  - exact (const_rd (ms_mem ms) cH Hc HcH ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply Hro; right; exact Hx)).
Qed.

End Memchr.
