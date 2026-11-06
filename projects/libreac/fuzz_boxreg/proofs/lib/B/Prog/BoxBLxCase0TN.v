(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 909 of its 980 lines of code are new or changed and 860 lines of the source are left out. *)
(* Case op & 3 = 0 of the B walk of LLVMFuzzerTestOneInput, piece T -> N: from LI_T 0 (0x8034c) through the
   switch, the two inlined fuzz_u8 (nch, base) and the call of read_name (&in) at 0x80520 to the cut C0_N
   (0x80524).
   The walk (c0tn): the seat c0tn_seat at T with the nb (0, 1 or 2) bytes left after the op byte; `blt s3, a0`
   (0x80354) and `bnez a0` (0x8035c) are not taken (op & 3 = 0); the fuzz_u8 n-checks `beqz a1` are taken at
   0x80364 (nb = 0) and at 0x80398 (nb = 1), and decided by the atom facts for nb = 2; the UBSan pointer checks
   (bgeu s3, a1) and the __asan_report_load1 shadow checks are decided by the cursor's atom fact and the input
   block's shadow entry. Every run writes only the spill slots [sp1, sp1 + 0x98) (c0tn_keep_step).
   The call (c0tn_call): read_name's contract (lh_read_name) on the cursor at sp1 + 0x88 (the caller's stack
   window: tbwr_ok, zero shadow) and the input left after nch and base (c0_pl2); its post gives the name block,
   the advanced cursor and tbcj_kept, which keeps every other byte C0_N reads (the slots below the cursor, the stack
   above it, the input, the frame and its shadow, r). *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import PaRun PaShadow PaJournal BoxBase YC4b.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBSyms BoxBList BoxBPa BoxBPaLib BoxBFrame.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import YC1g YC1h BoxBCJ BoxBReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.B.Prog Require Import BoxBLxDefs BoxBLxSeat BoxBLxCase0Defs.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg read_name_c LLVMFuzzerTestOneInput_case0
  LLVMFuzzerTestOneInput_rn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The input region of the piece: the nb (0, 1 or 2) bytes the two fuzz_u8 read at the cursor (atom 48), their
   values the atoms 50 and 51. *)
Definition c0tn_in_cs (nb : nat) : list YP09.chunk :=
  firstn nb [YP09.mkChunk 0 (CVal 1 (SOff 50%nat 0)); YP09.mkChunk 1 (CVal 1 (SOff 51%nat 0))].
Definition c0tn_in_region (nb : nat) : YP09.region :=
  YP09.mkRegion (Some 48%nat) 0 (Z.of_nat nb) 0 0 (c0tn_in_cs nb).
(* The slots the piece carries: the loop's (lslots_loop), the frame's and the cursor. *)
Definition c0tn_slots : list (Z * sv) :=
  [(0x08, SLit 3); (0x10, SOff LA_F 0); (0x18, SOff LA_F 0); (0x28, SOff 20%nat 280); (0x30, SOff 27%nat 0);
   (0x38, SLit 0); (0x40, SOff 52%nat 0); (0x68, SOff LA_F 32); (0x70, SOff 53%nat 0); (0x78, SOff 54%nat 0);
   (0x80, SOff LA_F 0); (0x88, SOff 48%nat 0); (0x90, SOff 49%nat 0)].
(* The bounds of the bytes left after the op byte: none, one, or two and more. *)
Definition c0tn_nrem_af (nb : nat) : afact :=
  match nb with O => mkAF 0 0 0 | S O => mkAF 1 1 0 | _ => mkAF 2 (2 ^ 26) 0 end.
Definition c0tn_facts (nb : nat) : facts :=
  mkFacts (LX_AF ++ [(48%nat, mkAF 4096 0x7fffff800000 0); (49%nat, c0tn_nrem_af nb);
                     (50%nat, mkAF 0 255 0); (51%nat, mkAF 0 255 0)]) [] [].
Definition c0tn_SB : Z := 0x7fff8000.
Definition c0tn_Bspan : Z * Z := (c0tn_SB, c0tn_SB + 2 ^ 44 - 1).

(* The bytes the facts of C0_N read below the stack, and the stack above the spill slots: none is a spill slot. *)
Lemma c0tn_rng : forall a sp1 p n F SH r ac,
  ac < sp1 -> sp1 <= 2 ^ 47 -> 4096 <= p -> p + n <= ac -> 4096 <= F -> F + 512 <= ac -> 0 <= SH -> SH + 64 <= ac ->
  4096 <= r -> r + 288 <= ac ->
  (sp1 + 0x98 <= a < 2 ^ 64 \/ p <= a < p + n \/ F <= a < F + 512 \/ SH <= a < SH + 64 \/ r <= a < r + 288) ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 <= a < sp1 + 152).
Proof. intros a sp1 p n F SH r ac H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Ha. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg boxb_listing}.
#[local] Notation SEGS := (@pa_segs _ boxb_listing PI).
#[local] Notation VAL := (@pa_val _ boxb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ boxb_listing PI).
#[local] Notation BASE := (@pa_val _ boxb_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HY : lx_hyps B MT.

Let LAWS := lh_laws B MT HY.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* The piece's own atoms: the cursor, the bytes left, the two bytes, shadow_addr (r + 280), ~r, ~prev. *)
Definition c0tn_ex (cx : lxcx) (fp r : Z) (pos : nat) : list word :=
  [w64 (lc_p cx + Z.of_nat (S pos)); w64 (lc_n cx - Z.of_nat (S pos));
   w64 (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0)));
   w64 (bv_unsigned (nth (S (S pos)) (lc_pl cx) (Z_to_bv 8 0)));
   w64 (shadow_addr (r + 280)); w64 (2 ^ 64 - 1 - r); w64 (2 ^ 64 - 1 - (lF cx fp + 64))].
Definition c0tn_sr : list sv := lx_sr (LX_OVP ++ [((19%bv : bv 5), SLit 1)]).

Lemma c0_atoms_ok_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
  intros E l1. induction l1 as [|[n f] l1 IH]; intros l2 H1 H2; cbn [app atoms_ok] in *; [exact H2|].
  destruct H1 as [Hf Hr]. split; [exact Hf | exact (IH l2 Hr H2)].
Qed.

Lemma c0_garr8_at : forall (m : word -> option byte) a (l : list byte) j,
  garr8 SEGS m a (map (fun b : byte => bv_unsigned b) l) -> (j < length l)%nat ->
  val_mem SEGS m (a + Z.of_nat j) 1 (bv_unsigned (nth j l (Z_to_bv 8 0))).
Proof.
  intros m a l j Hg Hj. destruct (Hg j ltac:(rewrite length_map; exact Hj)) as [Hv _].
  rewrite <- (map_nth (fun b : byte => bv_unsigned b) l (Z_to_bv 8 0) j). exact Hv.
Qed.

Lemma c0_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. Qed.

(* The seat at T, with nb of the bytes left after the op byte in the input region. *)
Lemma c0tn_seat : forall cx fp k ly3 S3 W3 ms3 md3 pos r fab (nb : nat),
  lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(LX_CID, fp)] ->
  lx_body cx fp LP_T W3 ms3 LSH_iter -> lblk B cx ly3 S3 r ->
  lcur cx W3 ms3 (S pos) -> lslots_loop cx fp W3 ms3 r fab ->
  getr (ms_regs ms3) 19 = w64 1 -> getr (ms_regs ms3) 20 = w64 r ->
  getr (ms_regs ms3) 21 = w64 (lF cx fp + 64) -> getr (ms_regs ms3) 27 = w64 fab ->
  ((nb = 0 /\ length (lc_pl cx) = S pos) \/ (nb = 1 /\ length (lc_pl cx) = S (S pos)) \/
   (nb = 2 /\ S (S pos) < length (lc_pl cx)))%nat ->
  st_ok_pi SEGS VAL (lx_env cx fp (ms_regs ms3) (c0tn_ex cx fp r pos))
    (lx_ss LP_T c0tn_sr LSH_iter (lx_slot_chunks c0tn_slots) [] 0 0 0 0 [c0tn_in_region nb] (c0tn_facts nb))
    (restrict (w_H W3) ms3) /\
  sh_ok SEGS (SOff LA_SB 0) [mkSHE 48 0 (Z.of_nat nb); mkSHE LA_F 512 0]
    (lx_env cx fp (ms_regs ms3) (c0tn_ex cx fp r pos)) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros cx fp k ly3 S3 W3 ms3 md3 pos r fab nb HB HJ HFR HBD Hblk Hcur Hsl H19 H20 H21 H27 Hnb.
  pose proof HBD as (Hpc & Hresv & Hsvc & Hrom & Hfreg & Hfcsr & HREGS & HSAVED & HSH & HFLAG
    & HS10 & HS18 & HS80 & HINP).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof HJ as (HAR3 & _).
  assert (Hrin : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin) as (Hr16 & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in *.
  pose proof HB as (_ & _ & _ & Hpn & _).
  pose proof Hcur as (HcurL & Hcur88 & Hcur90).
  assert (Hn : 0 < lc_n cx < 2 ^ 26 /\ In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx))).
  { destruct Hpn as [Hn0 | Hn]; [unfold lc_n in Hn0; lia | exact Hn]. }
  destruct Hn as [Hnr Hpin].
  assert (Hpin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hpin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin3) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
  assert (Hreq : req_size (lc_n cx) = lc_n cx) by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lc_n cx) 0) ltac:(lia)); reflexivity).
  rewrite Hreq in Hpceil, Hpia.
  set (E := lx_env cx fp (ms_regs ms3) (c0tn_ex cx fp r pos)).
  assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 _); exact HREGS).
  pose proof HE as (_ & _ & _ & _ & _ & HE32 & _ & HE46 & _).
  assert (EX : forall i, (i < 7)%nat -> ew E (LA_EX + i) = nth i (c0tn_ex cx fp r pos) (w64 0))
    by (intros i0 Hi0; apply lx_env_ex; lia).
  assert (E48 : ew E 48 = w64 (lc_p cx + Z.of_nat (S pos))) by exact (EX 0%nat ltac:(lia)).
  assert (E49 : ew E 49 = w64 (lc_n cx - Z.of_nat (S pos))) by exact (EX 1%nat ltac:(lia)).
  assert (E50 : ew E 50 = w64 (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0)))) by exact (EX 2%nat ltac:(lia)).
  assert (E51 : ew E 51 = w64 (bv_unsigned (nth (S (S pos)) (lc_pl cx) (Z_to_bv 8 0)))) by exact (EX 3%nat ltac:(lia)).
  assert (E52 : ew E 52 = w64 (shadow_addr (r + 280))) by exact (EX 4%nat ltac:(lia)).
  assert (E53 : ew E 53 = w64 (2 ^ 64 - 1 - r)) by exact (EX 5%nat ltac:(lia)).
  assert (E54 : ew E 54 = w64 (2 ^ 64 - 1 - (lF cx fp + 64))) by exact (EX 6%nat ltac:(lia)).
  assert (E20 : ew E 20 = w64 r) by (unfold E; rewrite (lx_env_reg cx fp _ _ 20 (20%bv : bv 5)) by reflexivity; exact H20).
  assert (E27 : ew E 27 = w64 fab) by (unfold E; rewrite (lx_env_reg cx fp _ _ 27 (27%bv : bv 5)) by reflexivity; exact H27).
  pose proof Hsl as (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  unfold lc_n in *.
  assert (Hlen : (S pos <= length (lc_pl cx))%nat) by exact HcurL.
  assert (Hfab : 0 <= fab < 2 ^ 64).
  { unfold lslot, lview in S30. exact (c0_rdword_range _ _ _ _ S30). }
  assert (RNG : forall off v, lslot cx W3 ms3 off v -> 0 <= v < 2 ^ 64)
    by (intros off v Hv; exact (c0_rdword_range _ _ _ _ Hv)).
  assert (HSL : lx_slots cx W3 ms3 E c0tn_slots).
  { unfold lx_slots, c0tn_slots.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
    - exact (lx_slot_lit cx W3 ms3 E 0x08 3 S08 ltac:(lia)).
    - apply (lx_slot_atom cx W3 ms3 E 0x10 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS10 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x18 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS18 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x28 20 r 280); [exact S28 | exact E20 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x30 27 fab 0); [rewrite Z.add_0_r; exact S30 | exact E27 | lia | lia].
    - exact (lx_slot_lit cx W3 ms3 E 0x38 0 S38 ltac:(lia)).
    - pose proof (RNG _ _ S40).
      apply (lx_slot_atom cx W3 ms3 E 0x40 52 (shadow_addr (r + 280)) 0); [rewrite Z.add_0_r; exact S40 | exact E52 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x68 LA_F (lF cx fp) 32); [exact S68 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x70 53 (2 ^ 64 - 1 - r) 0); [rewrite Z.add_0_r; exact S70 | exact E53 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x78 54 (2 ^ 64 - 1 - (lF cx fp + 64)) 0);
        [rewrite Z.add_0_r; exact S78 | exact E54 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x80 LA_F (lF cx fp) 0); [rewrite Z.add_0_r; exact HS80 | exact HE46 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x88 48 (lc_p cx + Z.of_nat (S pos)) 0);
        [rewrite Z.add_0_r; exact Hcur88 | exact E48 | lia | lia].
    - apply (lx_slot_atom cx W3 ms3 E 0x90 49 (Z.of_nat (length (lc_pl cx)) - Z.of_nat (S pos)) 0);
        [rewrite Z.add_0_r; exact Hcur90 | exact E49 | lia | lia]. }

  assert (Hcur0 : 0 <= lc_p cx + Z.of_nat (S pos) < 2 ^ 64) by lia.
  assert (U48 : U E (SOff 48 0) = lc_p cx + Z.of_nat (S pos)) by (apply U_atom; [exact E48 | lia]).
  assert (U32 : U E (SOff LA_SB 0) = SHADOW_OFF) by (apply U_atom; [exact HE32 | unfold SHADOW_OFF; lia]).
  assert (U46 : U E (SOff LA_F 0) = lF cx fp) by (apply U_atom; [exact HE46 | lia]).
  assert (B48 : bv_unsigned (ew E 48) = lc_p cx + Z.of_nat (S pos)) by (rewrite E48; apply unsigned_lit_small; lia).
  assert (HREG : regs_ok E c0tn_sr (ms_regs ms3)).
  { unfold c0tn_sr. apply lx_regs_ok; [apply lx_regs_ok_atoms |]. apply Forall_app. split.
    - apply (lx_ovp_ok cx fp ms3 _); [exact HREGS | exact H21].
    - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd sv_denot]. rewrite H19. reflexivity. }
  assert (HAF : atoms_ok E LX_AF) by exact (lx_af_ok B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE).
  destruct Hnb as [(-> & HL) | [(-> & HL) | (-> & HL)]].

  all: pose proof (c0_byte_range (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))).
  all: pose proof (c0_byte_range (nth (S (S pos)) (lc_pl cx) (Z_to_bv 8 0))).
  all: split;
    [ apply (lx_seat B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR); [exact HE | exact HBD | exact HREG | exact HSL
        | apply Forall_nil | lia | lia | lia | lia | vm_compute; reflexivity | | | | ]
    | apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
      [ apply (lx_shent_block B LAWS ly3 S3 W3 (ms_mem ms3) md3 E _ _ _ 0 _ 48 HAR3 Hpin3 U32 U48); [lia | lia | rewrite Hreq; lia]
      | exact (lx_shent_rev E _ (lF cx fp) 512 LA_F U32 U46 HFia ltac:(lia)) ] ].
  all: try (cbn; tauto).
  all: try (apply (lx_block_disj B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E 48 _ _ _ 0 _ 0 0 _ _ _ _ 0 0 0 0 HE Hpin3 B48);
          [lia | lia | rewrite Hreq; lia]).
  all: try (split; [|split; exact I]; unfold c0tn_facts; cbn [f_atoms]; apply c0_atoms_ok_app; [exact HAF|];
        cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2 c0tn_nrem_af];
        rewrite E48, E49, E50, E51; unfold w64;
        rewrite !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r;
        repeat match goal with |- _ /\ _ => split end; first [exact I | lia]).

  all: apply Forall_cons; [|apply Forall_nil]; unfold c0tn_in_region, c0tn_in_cs, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val firstn Z.of_nat];
    rewrite B48; (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
  - apply Forall_nil.
  - apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 50 0) (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))));
      [rewrite lx_sv_SOff0, E50; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (c0_garr8_at _ _ _ (S pos) HINP ltac:(lia)).
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 50 0) (bv_unsigned (nth (S pos) (lc_pl cx) (Z_to_bv 8 0))));
        [rewrite lx_sv_SOff0, E50; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (c0_garr8_at _ _ _ (S pos) HINP ltac:(lia)).
    + apply (chunk_ok_val SEGS E _ _ 1 1 (SOff 51 0) (bv_unsigned (nth (S (S pos)) (lc_pl cx) (Z_to_bv 8 0))));
        [rewrite lx_sv_SOff0, E51; reflexivity | cbn; lia | cbn; lia |].
      replace (lc_p cx + Z.of_nat (S pos) + 1) with (lc_p cx + Z.of_nat (S (S pos))) by lia.
      exact (c0_garr8_at _ _ _ (S (S pos)) HINP ltac:(lia)).
Qed.

(* ---- the bytes the walk keeps ---- *)
(* A run whose only write window is the spill area [sp1, sp1 + 152) keeps every other byte. *)
Lemma c0tn_keep_step : forall E rs H (m0 m1 m2 : word -> option byte) sp1,
  windows rs = [(Some 8%nat, 0, 0); (Some 2%nat, 0, 152); (Some 46%nat, 0, 0); (Some 22%nat, 0, 0); (Some 48%nat, 0, 0)] ->
  bv_unsigned (ew E 2) = sp1 ->
  frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 152) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 <= a < sp1 + 152) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
  intros E rs H m0 m1 m2 sp1 Hw Hsp HF K a Ha Hn. rewrite <- (K a Ha Hn).
  apply (kept_of_frame E rs H m1 m2 (fun x => sp1 <= x < sp1 + 152) HF); [|exact Ha|exact Hn].
  intros b wlo whi x Hin Hx. rewrite Hw in Hin. cbn [In] in Hin.
  destruct Hin as [Hi|[Hi|[Hi|[Hi|[Hi|[]]]]]]; injection Hi as <- <- <-; cbn [base_val] in Hx; rewrite ?Hsp in Hx; lia.
Qed.

(* A word, across two memories (and worlds) that agree on its eight bytes. *)
Lemma c0tn_rd_x : forall (Wa Wb : world SEGS) ma mb a v,
  (forall j, 0 <= j < 8 -> aview SEGS (w_H Wb) mb (a + j) = aview SEGS (w_H Wa) ma (a + j)) ->
  rdword (aview SEGS (w_H Wa) ma) a = Some v -> rdword (aview SEGS (w_H Wb) mb) a = Some v.
Proof.
  intros Wa Wb ma mb a v K Hr.
  pose proof (K 0 ltac:(lia)) as K0. rewrite Z.add_0_r in K0.
  pose proof (K 1 ltac:(lia)) as K1. pose proof (K 2 ltac:(lia)) as K2.
  pose proof (K 3 ltac:(lia)) as K3. pose proof (K 4 ltac:(lia)) as K4.
  pose proof (K 5 ltac:(lia)) as K5. pose proof (K 6 ltac:(lia)) as K6.
  pose proof (K 7 ltac:(lia)) as K7.
  unfold rdword in Hr |- *. rewrite K0, K1, K2, K3, K4, K5, K6, K7. exact Hr.
Qed.

(* A spill slot from the spill region's chunk of a symbolic state. *)
Lemma c0tn_slot_of : forall E m cs lo hi wlo whi off e v sp1,
  region_ok SEGS E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = sp1 ->
  In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (sp1 + off) 8 v.
Proof.
  intros E m cs lo hi wlo whi off e v sp1 HR Hb Hin He Hv.
  exact (field_of_region E m 2 sp1 cs lo hi wlo whi off 8%N e v HR Hb Hin He
           ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma c0tn_bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof.
  intros l1 l2. induction l1 as [|x l IH].
  - change ([] ++ l2) with l2. change (bsum []) with 0. lia.
  - change ((x :: l) ++ l2) with (x :: (l ++ l2)). change (bsum (x :: (l ++ l2))) with (snd x + bsum (l ++ l2)).
    change (bsum (x :: l)) with (snd x + bsum l). rewrite IH. lia.
Qed.

(* The machine stack's shadow is zero (AR's zero-shadow law over the layout's stack range). *)
Lemma c0tn_stk_ra : forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md ->
  ly_stk_lo ly <= a -> a + n <= ly_stk_hi ly -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
  intros ly S W mem md a n HAR Hlo Hhi x Hx.
  pose proof HAR as (M & _). pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5, T6.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    (or_introl eq_refl)) as Z0.
  cbn [fst snd] in Z0.
  exists 0. split; [|left; reflexivity].
  pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as D1.
  pose proof (Z.div_mod (ly_stk_hi ly) 4096 ltac:(lia)) as D2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D4.
  rewrite T5, Z.add_0_r in D1. rewrite T6, Z.add_0_r in D2.
  set (ql := ly_stk_lo ly / 4096) in *. set (qh := ly_stk_hi ly / 4096) in *.
  assert (E1 : ly_stk_lo ly / 8 = 512 * ql) by (rewrite D1; replace (4096 * ql) with ((512 * ql) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (ly_stk_hi ly - ly_stk_lo ly) / 8 = 512 * (qh - ql))
    by (rewrite D1, D2; replace (4096 * qh - 4096 * ql) with ((512 * (qh - ql)) * 8) by lia; apply Z.div_mul; lia).
  specialize (Z0 (x / 8 - 512 * ql)). rewrite E2 in Z0.
  unfold shadow_of_addr in Z0 |- *. rewrite E1 in Z0.
  replace (SHADOW_OFF + 512 * ql + (x / 8 - 512 * ql)) with (SHADOW_OFF + x / 8) in Z0 by lia.
  apply Z0. lia.
Qed.

(* A byte of the caller's stack window: the caller's journal may let a callee write it. *)
Lemma c0tn_stack_win : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= a < sp0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ apresent (w_H W) memc a /\
  ~ aowned B lyc Sc a /\ ly_stk_lo lyc <= a < ly_stk_hi lyc.
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ Ha.
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  assert (Hs : ly_stk_lo lyc <= a < ly_stk_hi lyc) by lia.
  split; [left; exact Ha|]. split; [exact (Hpres a Ha)|]. split; [|exact Hs].
  exact (al_stack _ _ LAWS lyc Sc W memc mdc a HAR Hs).
Qed.

(* A byte of a block older than the new block (the name) lies apart from it. *)
Lemma c0tn_new_apart : forall ly2 S2 (W2 : world SEGS) mem2 md2 ly3 S3 s n b m j,
  AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B ly3 S3 ++ [(s, n)] -> 0 < n ->
  In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m -> ~ (s <= b + j < s + n).
Proof.
  intros ly2 S2 W2 mem2 md2 ly3 S3 s n b m j HAR E Hn Hb Hj Hs.
  assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (rewrite E; apply in_or_app; left; exact Hb).
  assert (Hs2 : In (s, n) (ablocks B ly2 S2)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (Hd : {(b, m) = (s, n)} + {(b, m) <> (s, n)}) by (decide equality; apply Z.eq_dec).
  destruct Hd as [Ee | Ne].
  - apply in_split in Hb as (l1 & l2 & El). rewrite Ee in El.
    pose proof (sep_blocks_pos SEGS B LAWS ly2 S2 W2 mem2 md2 (s, n) (s, n) l1 l2 [] HAR) as D.
    rewrite E, El, <- app_assoc in D. specialize (D eq_refl).
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. pose proof (req_size_pos n ltac:(lia)) as [Hq _]. lia.
  - pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m s n HAR Hb2 Hs2 Ne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. lia.
Qed.

(* A byte read as a signed value: itself, or itself less 256. *)
Lemma c0tn_sbyte : forall b : byte,
  (bv_unsigned b < 128 /\ bv_signed b = bv_unsigned b) \/ (128 <= bv_unsigned b /\ bv_signed b = bv_unsigned b - 256).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  change (256 / 2) with 128.
  destruct (Z_lt_le_dec (bv_unsigned b) 128) as [Hl | Hh].
  - left. split; [exact Hl|]. rewrite Z.mod_small by lia. lia.
  - right. split; [exact Hh|]. rewrite <- (Z.mod_unique (bv_unsigned b + 128) 256 1 (bv_unsigned b - 128)) by lia. lia.
Qed.

Lemma c0tn_w64_mod : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof.
  intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_mod. lia.
Qed.

(* The base byte as the code keeps it: shifted to the top byte (sp1 + 0x50), and sign-extended back (s10). *)
Lemma c0tn_shl : forall E n (b : byte), ew E n = w64 (bv_unsigned b) ->
  sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 56)) = w64 ((bv_signed b * 2 ^ 56) mod 2 ^ 64).
Proof.
  intros E n b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n (bv_unsigned b) H) by lia.
  rewrite U_lit by lia. change (Z.land 56 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
  unfold zcanon, M64, w64. f_equal.
  destruct (c0tn_sbyte b) as [(_ & ->) | (_ & ->)]; [reflexivity|].
  replace ((bv_unsigned b - 256) * 2 ^ 56) with (bv_unsigned b * 2 ^ 56 + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma c0tn_sext : forall E n (b : byte), ew E n = w64 (bv_unsigned b) ->
  sv_denot E (SAlu ALU_SRA (SAlu ALU_SLL (SOff n 0) (SLit 56)) (SLit 56)) = w64 (bv_signed b).
Proof.
  intros E n b H. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  rewrite denot_lit_U, U_SAlu, U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n (bv_unsigned b) H) by lia.
  rewrite !U_lit by lia. change (Z.land 56 63) with 56. rewrite Z.shiftl_mul_pow2 by lia.
  unfold zcanon, M64, w64. rewrite c0tn_w64_mod.
  rewrite (Z.mod_small (bv_unsigned b * 2 ^ 56) (2 ^ 64)) by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  rewrite Z.shiftr_div_pow2 by lia. f_equal. change (2 ^ 64 / 2) with (2 ^ 63).
  destruct (c0tn_sbyte b) as [(Hl & ->) | (Hh & ->)].
  - rewrite Z.mod_small by lia. replace (bv_unsigned b * 2 ^ 56 + 2 ^ 63 - 2 ^ 63) with (bv_unsigned b * 2 ^ 56) by lia.
    apply Z.div_mul. lia.
  - rewrite <- (Z.mod_unique (bv_unsigned b * 2 ^ 56 + 2 ^ 63) (2 ^ 64) 1 (bv_unsigned b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64)) by lia.
    replace (bv_unsigned b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64 - 2 ^ 63) with ((bv_unsigned b - 256) * 2 ^ 56) by lia.
    apply Z.div_mul. lia.
Qed.

(* The case's values from the bytes left after the op byte. *)
Lemma c0tn_vals0 : forall (pl : list byte) pos, length pl = S pos -> c0_nchv pl pos = 0 /\ c0_basev pl pos = 0.
Proof.
  intros pl pos HL. unfold c0_nchv, c0_basev, c0_pl0. rewrite skipn_all2 by lia. split; reflexivity.
Qed.

Lemma c0tn_vals1 : forall (pl : list byte) pos, (S pos < length pl)%nat ->
  c0_nchv pl pos = bv_unsigned (nth (S pos) pl (Z_to_bv 8 0)).
Proof.
  intros pl pos HL. unfold c0_nchv, c0_pl0.
  destruct (skipn (S pos) pl) as [|x t] eqn:Es.
  - exfalso. pose proof (f_equal (@length byte) Es) as L. rewrite length_skipn in L. cbn in L. lia.
  - cbn [LLVMFuzzerTestOneInput_case0.c0_nch]. rewrite <- (Nat.add_0_r (S pos)), <- nth_skipn, Es. reflexivity.
Qed.

Lemma c0tn_vals1b : forall (pl : list byte) pos, length pl = S (S pos) -> c0_basev pl pos = 0.
Proof.
  intros pl pos HL. unfold c0_basev, c0_pl0.
  destruct (skipn (S pos) pl) as [|x [|y t]] eqn:Es; [reflexivity | reflexivity|].
  exfalso. pose proof (f_equal (@length byte) Es) as L. rewrite length_skipn in L. cbn in L. lia.
Qed.

Lemma c0tn_vals2 : forall (pl : list byte) pos, (S (S pos) < length pl)%nat ->
  c0_basev pl pos = bv_signed (nth (S (S pos)) pl (Z_to_bv 8 0)).
Proof.
  intros pl pos HL. unfold c0_basev, c0_pl0.
  destruct (skipn (S pos) pl) as [|x [|y t]] eqn:Es.
  - exfalso. pose proof (f_equal (@length byte) Es) as L. rewrite length_skipn in L. cbn in L. lia.
  - exfalso. pose proof (f_equal (@length byte) Es) as L. rewrite length_skipn in L. cbn in L. lia.
  - cbn [LLVMFuzzerTestOneInput_case0.c0_base]. f_equal.
    replace (S (S pos)) with (S pos + 1)%nat by lia. rewrite <- nth_skipn, Es. reflexivity.
Qed.

(* A register of the symbolic state at a call. *)
Lemma c0tn_reg : forall Ex ss H ms (x : bv 5) e v,
  st_ok SEGS Ex ss (restrict H ms) -> sr_get (ss_regs ss) x = e -> sv_denot Ex e = v -> getr (ms_regs ms) x = v.
Proof. intros Ex ss H ms x e v HS He Hv. rewrite (st_ok_restrict_reg SEGS H Ex ss ms x HS), He. exact Hv. Qed.

Lemma c0tn_den_atom : forall E n v c, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = w64 (v + c).
Proof.
  intros E n v c H Hv. cbn [sv_denot]. rewrite H. unfold w64. rewrite unsigned_lit_small by exact Hv. reflexivity.
Qed.

(* ---- the call of read_name (&in) at 0x80520 and the cut C0_N at its return address ---- *)
(* From the machine state at the call (the walk's facts: the bytes outside the spill slots as at T, the registers and
   the slots), read_name's contract (lh_read_name) and its post give C0_N. *)
Lemma c0tn_call : forall POST i cx fp k acc ly3 S3 W3 (ms3 msc : machine_state) mdc pos r fab op bs,
  lx_from B MT POST (C0_N B MT i) -> lx_base B MT cx ->
  ajournal SEGS B LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
    [(LX_CID, fp)] ly3 S3 W3 (ms_mem msc) mdc k ->
  frames S3 = [(LX_CID, fp)] -> mo_le MT (lc_S cx) S3 acc ->
  lx_body cx fp LP_T W3 ms3 LSH_iter -> (i < 64)%nat -> k <= 1 + 2 * Z.of_nat i ->
  acc <= LX_A1 MT + Z.of_nat i * LX_AI MT ->
  lblk B cx ly3 S3 r -> lreg W3 ms3 r bs -> Boxreg.boxreg_inv bs -> Boxreg.bx_fabric bs = fab ->
  lprev cx fp W3 ms3 bs ->
  (pos < length (lc_pl cx))%nat -> op = bv_unsigned (nth pos (lc_pl cx) (Z_to_bv 8 0)) -> Z.land op 3 = 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + 152) ->
     aview SEGS (w_H W3) (ms_mem msc) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  lregs cx fp msc -> getr (ms_regs msc) 1 = w64 (BASE + C0P_N) ->
  getr (ms_regs msc) 10 = w64 (lsp1 cx + 0x88) ->
  getr (ms_regs msc) 20 = w64 r -> getr (ms_regs msc) 21 = w64 (lF cx fp + 64) ->
  getr (ms_regs msc) 23 = w64 op -> getr (ms_regs msc) 25 = w64 (c0_nchv (lc_pl cx) pos) ->
  getr (ms_regs msc) 26 = w64 (c0_basev (lc_pl cx) pos) -> getr (ms_regs msc) 27 = w64 fab ->
  lslots_loop cx fp W3 msc r fab -> lslot cx W3 msc 0x10 (lF cx fp) -> lslot cx W3 msc 0x18 (lF cx fp) ->
  lslot cx W3 msc 0x80 (lF cx fp) -> lslot cx W3 msc 0x48 (Boxreg.bx_n bs) ->
  lslot cx W3 msc 0x50 ((c0_basev (lc_pl cx) pos * 2 ^ 56) mod 2 ^ 64) -> lslot cx W3 msc 0x58 (Z.of_nat i) ->
  lcur cx W3 msc (c0_pos1 (lc_pl cx) pos) ->
  SRr SEGS W3 (mkCfg (mkst (ms_regs msc) (Z_to_bv 64 (SIGMA BB_read_name)) (ms_mem msc) (seg_rom SEGS)) mdc)
    (POST cx).
Proof.
  intros POST i cx fp k acc ly3 S3 W3 ms3 msc mdc pos r fab op bs HN HB HJ HFR HMO HBD Hi Hk Hacc Hblk Hreg Hinv
    Hfab Hprev Hpos Hop Hop3 KR HRG R1 R10 R20 R21 R23 R25 R26 R27 Hsl S10 S18 S80 S48 S50 S58 Hcur.
  pose proof HBD as (_ & _ & _ & _ & _ & _ & _ & HSAVED & HSH & HFLAG & _ & _ & _ & HINP).
  pose proof HRG as (G2 & G8 & G9 & G3 & G4 & G18 & G22).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 msc ly3 S3 mdc k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof (lx_frame_addr_eq B MT LAWS cx fp W3 msc ly3 S3 mdc k HB HJ) as EF.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_boxb) (PI := PI)) as HBLO.
  pose proof HB as (HPRE0 & _ & _ & Hpn & _ & _ & Hev & Hlive & HROD & HMOK & HNEED & HTR).
  pose proof HPRE0 as (HAR0 & _ & _ & Hgp & Htp & _).
  pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev & _).
  pose proof (lh_mtl B MT HY) as MTL.
  assert (Hfin : In (LX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes LX_CID = 512) by (vm_compute; reflexivity).
  assert (HFd : 0 <= lF cx fp / 8 /\ 8 * (lF cx fp / 8) <= lF cx fp).
  { split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]. }
  (* the input block *)
  assert (Hn : 0 < lc_n cx < 2 ^ 26 /\ In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx))).
  { destruct Hpn as [Hn0 | Hn]; [unfold lc_n in *; lia | exact Hn]. }
  destruct Hn as [Hnr Hpin].
  assert (Hpin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hpin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin3) as (Hp16 & Hp4096 & Hpceil & Hpia & _).
  assert (Hreq : req_size (lc_n cx) = lc_n cx)
    by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lc_n cx) 0) ltac:(lia)); reflexivity).
  rewrite Hreq in Hpceil, Hpia.
  assert (Hrin3 : In (r, LX_REG) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r LX_REG HAR3 Hrin3) as (_ & Hr4096 & Hrceil & Hria & _).
  change (req_size LX_REG) with 288 in Hrceil, Hria.
  assert (HIN : forall q, (q < length (lc_pl cx))%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (lc_p cx + Z.of_nat q) = Some (bv_unsigned (nth q (lc_pl cx) (Z_to_bv 8 0)))).
  { intros q Hq. apply (aview_of_val_mem1 SEGS); [exact (c0_garr8_at _ _ _ q HINP Hq) | apply c0_byte_range]. }
  (* what read_name reads: pl, the input after nch and base, at p *)
  set (pl := c0_pl2 (lc_pl cx) pos) in *.
  assert (Hu : LLVMFuzzerTestOneInput_case0.c0_used (c0_pl0 (lc_pl cx) pos) =
               Z.min (Z.of_nat (length (lc_pl cx)) - Z.of_nat (S pos)) 2)
    by (unfold LLVMFuzzerTestOneInput_case0.c0_used, c0_pl0; rewrite length_skipn; lia).
  assert (Hpos1 : Z.of_nat (c0_pos1 (lc_pl cx) pos) =
                  Z.of_nat (S pos) + Z.min (Z.of_nat (length (lc_pl cx)) - Z.of_nat (S pos)) 2).
  { unfold c0_pos1. rewrite Nat2Z.inj_add, Z2Nat.id by (rewrite Hu; lia). rewrite Hu. reflexivity. }
  assert (Lpl : Z.of_nat (length pl) = lc_n cx - Z.of_nat (c0_pos1 (lc_pl cx) pos)).
  { unfold pl, c0_pl2, c0_pl0. rewrite !length_skipn. unfold lc_n. rewrite Hpos1. lia. }
  pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range pl) as (Hrk & Hrk2).
  set (p := lc_p cx + Z.of_nat (c0_pos1 (lc_pl cx) pos)) in *.
  assert (Usp : spZ (ms_regs msc) = lsp1 cx) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
  pose proof Hcur as (HcL & C88 & C90).
  assert (HSTKB : READ_NAME_STKB = 16432) by reflexivity.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Hsp1m : lsp1 cx mod 16 = 0 /\ (lsp1 cx + 0x88) mod 8 = 0).
  { destruct (Z.mod_divide (lsp1 cx) 32 ltac:(lia)) as [Hd _]. destruct (Hd Hsp32) as [q Hq].
    split; apply Z.mod_divide; try lia; [exists (2 * q) | exists (4 * q + 17)]; lia. }
  assert (WIN : forall a, lsp1 cx + 0x88 <= a < lsp1 cx + 0x88 + 16 ->
    awr_byte LX_STK (lsp0 cx) [] (ablocks B (lc_ly cx) (lc_S cx)) (ablocks B ly3 S3) ly3 [(LX_CID, fp)] a /\
    apresent (w_H W3) (ms_mem msc) a /\ ~ aowned B ly3 S3 a /\ ly_stk_lo ly3 <= a < ly_stk_hi ly3)
    by (intros a Ha; apply (c0tn_stack_win _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ); unfold LX_STK; lia).
  rewrite pa_sigma_read_name.
  eapply SRr_bind.
  { apply (lh_read_name B MT HY LX_STK (lsp0 cx) [] (lc_ly cx) (lc_S cx) (lc_W cx) (lc_mem cx) (lc_md cx)
      [(LX_CID, fp)] ly3 S3 W3 (ms_mem msc) mdc k (ms_regs msc) (lsp1 cx + 0x88) p (lc_p cx) (lc_n cx) pl HJ).
    - rewrite R1. apply ret_ok_codeptr_v; [unfold C0P_N; lia | reflexivity].
    - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by (unfold C0P_N; lia). unfold C0P_N. lia.
    - rewrite G3. exact Hgp.
    - rewrite G4. exact Htp.
    - rewrite Usp. exact (proj1 Hsp1m).
    - rewrite Usp, HSTKB. unfold LX_STK. lia.
    - rewrite Usp. lia.
    - exact R10.
    - exact (proj2 Hsp1m).
    - rewrite Usp. lia.
    - exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem msc) _ _ C88).
    - rewrite Lpl. replace (lsp1 cx + 136 + 8) with (lsp1 cx + 144) by lia.
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem msc) _ _ C90).
    - destruct (WIN (lsp1 cx + 0x88) ltac:(lia)) as (_ & _ & _ & Wl & _).
      destruct (WIN (lsp1 cx + 0x88 + 15) ltac:(lia)) as (_ & _ & _ & _ & Wh).
      exact (c0tn_stk_ra ly3 S3 W3 (ms_mem msc) mdc (lsp1 cx + 0x88) 16 HAR3 Wl ltac:(lia)).
    - intros a Ha. destruct (WIN a Ha) as (Wa & Wp & Wo & _). split; [exact Wa|]. split; [exact Wp|].
      split; [exact Wo|]. rewrite Usp, Hes. lia.
    - unfold p. lia.
    - rewrite Lpl. unfold p. lia.
    - rewrite Lpl. apply (amem_range_sub_app (lc_p cx) (lc_n cx)); [exact Hpia | lia | unfold p; lia | unfold p; lia | lia].
    - intros _. rewrite Lpl. split; [exact Hpin3|]. unfold p. split; lia.
    - intros j Hj. rewrite Lpl in Hj.
      assert (Hu2 : Z.of_nat (c0_pos1 (lc_pl cx) pos) = Z.of_nat (S pos) + 2) by (rewrite Hpos1; unfold lc_n in Hj; lia).
      rewrite KR by (unfold p; lia).
      unfold pl, c0_pl2, c0_pl0. rewrite skipn_skipn, nth_skipn.
      replace (p + j) with (lc_p cx + Z.of_nat (2 + S pos + Z.to_nat j)) by (unfold p; lia).
      apply HIN. unfold lc_n in Hj. lia.
    - unfold EV_READ_NAMEB, LX_EV in *. lia.
    - pose proof Hblk as Hb2. unfold lblk in Hb2.
      rewrite (blocks_bytes_bsum B ly3 S3), Hb2, c0tn_bsum_app.
      rewrite (blocks_bytes_bsum B (lc_ly cx) (lc_S cx)) in Hlive.
      cbn [bsum fold_right snd]. unfold LX_LIVE, LIVE_READ_NAMEB, LX_REG in *. lia.
    - apply (mok_station MT (lc_S cx) S3 (lc_T cx) acc _ MTL HMOK HMO); [apply mo_malloc_nonneg; [exact MTL | lia]|].
      pose proof (mo_malloc_mono MT MTL (read_name_c.rn_k pl + 1) 48 ltac:(lia)) as M1.
      pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as M2. pose proof (mo_free_nonneg MT MTL) as M3.
      assert (Hm : (Z.of_nat i + 1) * LX_AI MT <= 64 * LX_AI MT)
        by (apply Z.mul_le_mono_nonneg_r; [unfold LX_AI; lia | lia]).
      unfold LX_AI in Hm |- *. unfold LX_AI in Hacc. unfold LX_NEED, LX_AI in HNEED. lia.
    - exact (lh_rn_trace B MT HY). }

  cbv beta.
  intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & s & -> & HJ2 & HP2 & R10' & Hfr2 & Hs4096 & Hab2 & _ & Haft & Hname
    & Hc1 & Hc2 & Hmle & Hkept).
  rewrite Usp in Hkept.
  pose proof HJ2 as (HAR2 & _).
  assert (HFR2 : frames S2 = [(LX_CID, fp)]) by (rewrite Hfr2; exact HFR).
  assert (Hsin : In (s, read_name_c.rn_k pl + 1) (ablocks B ly2 S2))
    by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hsin) as (_ & _ & Hsceil & Hsia & _).
  pose proof (req_size_pos (read_name_c.rn_k pl + 1) ltac:(lia)) as [Hsq0 Hsq].
  assert (Hfin2 : In (LX_CID, fp) (frames S2)) by (rewrite HFR2; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ LX_CID fp HAR2 Hsin Hfin2) as Dsf.
  unfold zdisjoint in Dsf. cbn [fst snd] in Dsf. rewrite Hfb in Dsf.
  rewrite (lx_frame_addr_eq B MT LAWS cx fp W2 (mkst regs2 (w64 (BASE + C0P_N)) mem2 (seg_rom SEGS)) ly2 S2 md2
             (k + EV_READ_NAMEB) HB HJ2) in Dsf.
  destruct Hkept as (K1 & K2 & _ & K4 & _).
  assert (Hspc : alloc_ceiling < lsp1 cx) by lia.
  (* the bytes the call keeps: the slots below the cursor, the stack above it, the input, the frame and its shadow, r *)
  assert (KP2 : forall a, (lsp1 cx <= a < lsp1 cx + 0x88 \/ lsp1 cx + 0x98 <= a < 2 ^ 64 \/
       lc_p cx <= a < lc_p cx + lc_n cx \/ lF cx fp <= a < lF cx fp + 512 \/ lSH cx fp <= a < lSH cx fp + 64 \/
       r <= a < r + 288) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem msc) a).
  { intros a Ha. destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
    - apply K1; [lia | rewrite HSTKB; lia | unfold read_name_c.rn_writes; lia].
    - apply K1; [lia | rewrite HSTKB; lia | unfold read_name_c.rn_writes; lia].
    - pose proof (c0tn_new_apart ly2 S2 W2 mem2 md2 ly3 S3 s _ (lc_p cx) (lc_n cx) (a - lc_p cx) HAR2 Hab2
        ltac:(lia) Hpin3 ltac:(rewrite Hreq; lia)) as Na.
      replace a with (lc_p cx + (a - lc_p cx)) in Na |- * by lia.
      apply (K2 (lc_p cx) (lc_n cx) (a - lc_p cx) Hpin3); [rewrite Hreq; lia|].
      unfold read_name_c.rn_writes. lia.
    - apply (K4 LX_CID fp a Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EF, Hfb; lia|].
      unfold read_name_c.rn_writes. lia.
    - apply (K4 LX_CID fp a Hfin).
      + right. unfold in_zr. cbn [fst snd]. rewrite EF, Hfb. change (512 / 8) with 64. exact Ha.
      + unfold read_name_c.rn_writes. rewrite HSHeq in Ha.
        revert Hsia Ha HFd HFc C1 C2 C3 C4 C5 Hsq Hsceil Hspc. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
        clear. intros. lia.
    - pose proof (c0tn_new_apart ly2 S2 W2 mem2 md2 ly3 S3 s _ r LX_REG (a - r) HAR2 Hab2
        ltac:(lia) Hrin3 ltac:(change (req_size LX_REG) with 288; lia)) as Na.
      replace a with (r + (a - r)) in Na |- * by lia.
      apply (K2 r LX_REG (a - r) Hrin3); [change (req_size LX_REG) with 288; lia|].
      unfold read_name_c.rn_writes. lia. }
  assert (KP3 : forall a, (lsp1 cx + 0x98 <= a < 2 ^ 64 \/ lc_p cx <= a < lc_p cx + lc_n cx \/
       lF cx fp <= a < lF cx fp + 512 \/ lSH cx fp <= a < lSH cx fp + 64 \/ r <= a < r + 288) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite KP2 by tauto.
    assert (Hsh0 : 0 <= lSH cx fp) by (rewrite HSHeq; unfold SHADOW_OFF; lia).
    assert (Hsh1 : lSH cx fp + 64 <= alloc_ceiling) by (rewrite HSHeq; unfold SHADOW_OFF in *; lia).
    assert (HR : 0 <= a < 2 ^ 64 /\ ~ (lsp1 cx <= a < lsp1 cx + 152))
      by (apply (c0tn_rng a (lsp1 cx) (lc_p cx) (lc_n cx) (lF cx fp) (lSH cx fp) r alloc_ceiling);
          first [assumption | lia]).
    apply KR; tauto. }
  assert (SLX : forall off v, 0 <= off -> off + 8 <= 0x88 -> lslot cx W3 msc off v ->
      lslot cx W2 (mkst regs2 (w64 (BASE + C0P_N)) mem2 (seg_rom SEGS)) off v)
    by (intros off v H0 H1 Hv; apply (c0tn_rd_x W3 W2 (ms_mem msc) mem2); [intros j Hj; apply KP2; left; lia | exact Hv]).
  assert (KP : forall x : bv 5, acallee_saved (bv_unsigned x) -> getr regs2 x = getr (ms_regs msc) x)
    by (intros x Hx; pose proof (HP2 (bv_unsigned x) Hx) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
  assert (Hused : 0 <= tbread_name_used pl <= Z.of_nat (length pl)) by (unfold tbread_name_used; lia).
  rewrite R1.
  apply (HN cx fp (k + EV_READ_NAMEB) (acc + mo_malloc MT (read_name_c.rn_k pl + 1)) ly2 S2 W2
           (mkst regs2 (w64 (BASE + C0P_N)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR2).
  { exact (mle_station MT (lc_S cx) S3 S2 acc _ MTL HMO Hmle). }
  exists pos, r, fab, op, s, bs.
  split.
  { (* c0_com *)
    split.
    { split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|].
      split.
      { cbn [ms_regs mkst].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G2|].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G8|].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G9|].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G3|].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G4|].
        split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G18|].
        rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact G22. }
      split.
      { destruct HSAVED as (Hra & Hsj). split.
        - apply (c0tn_rd_x W3 W2 (ms_mem ms3) mem2); [intros j Hj; apply KP3; left; lia | exact Hra].
        - intros j Hj. apply (c0tn_rd_x W3 W2 (ms_mem ms3) mem2); [intros j' Hj'; apply KP3; left; lia | exact (Hsj j Hj)]. }
      split.
      { intros q Hq. unfold lview. cbn [ms_mem mkst]. rewrite KP3; [exact (HSH q Hq)|].
        change (length LSH_iter) with 52%nat in Hq. lia. }
      split.
      { rewrite Hfb in HFLAG |- *. apply (c0tn_rd_x W3 W2 (ms_mem ms3) mem2); [intros j Hj; apply KP3; lia | exact HFLAG]. }
      split; [apply SLX; [lia | lia | exact S10]|].
      split; [apply SLX; [lia | lia | exact S18]|].
      split; [apply SLX; [lia | lia | exact S80]|].
      intros j Hj. destruct (HINP j Hj) as [Hv Hbd]. split; [|exact Hbd].
      intros kk Hkk. assert (kk = 0)%nat by lia. subst kk.
      pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0 |- *. rewrite Z.add_0_r in Hv0 |- *.
      rewrite length_map in Hj. cbn [ms_mem mkst].
      rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W2) (ms_mem ms3) mem2 _
                 (KP3 (lc_p cx + Z.of_nat j) ltac:(unfold lc_n; lia))).
      exact Hv0. }
    split; [exact Hi|].
    split; [intros q Hq; unfold lview; cbn [ms_mem mkst]; rewrite KP3 by (unfold LX_REG in Hq; lia); exact (Hprev q Hq)|].
    split; [exact Hinv|]. split; [exact Hfab|]. split; [exact Hpos|]. split; [exact Hop|]. split; [exact Hop3|].
    split.
    { destruct Hsl as (L08 & L28 & L30 & L38 & L40 & L68 & L70 & L78).
      split; [apply SLX; [lia | lia | exact L08]|]. split; [apply SLX; [lia | lia | exact L28]|].
      split; [apply SLX; [lia | lia | exact L30]|]. split; [apply SLX; [lia | lia | exact L38]|].
      split; [apply SLX; [lia | lia | exact L40]|]. split; [apply SLX; [lia | lia | exact L68]|].
      split; [apply SLX; [lia | lia | exact L70]|]. apply SLX; [lia | lia | exact L78]. }
    split; [apply SLX; [lia | lia | exact S58]|].
    split; [apply SLX; [lia | lia | exact S48]|].
    cbn [ms_regs mkst].
    split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R20|].
    split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R21|].
    rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R27. }
  split.
  { (* c0_nm *)
    split; [unfold EV_READ_NAMEB; lia|].
    split; [unfold c0_nk; fold pl; lia|].
    split; [rewrite Hab2; unfold lblk in Hblk; rewrite Hblk, <- app_assoc; reflexivity|].
    split; [exact Haft|].
    split; [exact Hs4096|].
    split; [intros j Hj; exact (Hname j Hj)|].
    assert (Hp2 : Z.of_nat (c0_pos2 (lc_pl cx) pos) = Z.of_nat (c0_pos1 (lc_pl cx) pos) + tbread_name_used pl)
      by (unfold c0_pos2; fold pl; rewrite Nat2Z.inj_add, Z2Nat.id by lia; reflexivity).
    split; [unfold lc_n in Lpl; lia|].
    unfold lslot, lview. cbn [ms_mem mkst]. split.
    - rewrite Hp2. replace (lc_p cx + (Z.of_nat (c0_pos1 (lc_pl cx) pos) + tbread_name_used pl))
        with (p + tbread_name_used pl) by (unfold p; lia).
      apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc1 | unfold p; lia].
    - rewrite Hp2. replace (lc_n cx - (Z.of_nat (c0_pos1 (lc_pl cx) pos) + tbread_name_used pl))
        with (Z.of_nat (length pl) - tbread_name_used pl) by lia.
      replace (lsp1 cx + 144) with (lsp1 cx + 136 + 8) by lia.
      apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc2 | lia]. }
  split; [intros q Hq; unfold lview; cbn [ms_mem mkst]; rewrite KP3 by (unfold LX_REG in Hq; lia); exact (Hreg q Hq)|].
  split.
  { cbn [ms_regs mkst].
    split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R23|].
    split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R25|].
    split; [rewrite KP by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact R26|].
    apply SLX; [lia | lia | exact S50]. }
  cbn [ms_regs mkst]. exact R10'.
Qed.

(* ---- the walk T -> the call of read_name ---- *)
Ltac c0tn_awr2 HU2 d :=
  cbn [ss_mem add_cond lx_ss];
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ LA_SP d);
  [ reflexivity | unfold LA_SP; rewrite ?ew_ewset_other by lia; rewrite HU2; lia | cbn; unfold LX_STK; lia
  | cbn; unfold LX_SPILL; lia | ];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* After a run: the bytes outside the spill slots stay as at T (KEEP), and the model is named. *)
Ltac c0tn_after U2 cx KEEP :=
  lazymatch goal with
  | HFx : frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
    let K2 := fresh "K" in
    pose proof (c0tn_keep_step Ex rs H _ m1 m2 (lsp1 cx) ltac:(vm_compute; reflexivity)
                  ltac:(rewrite ?ew_ewset_other by lia; exact U2) HFx KEEP) as K2;
    clear KEEP HFx; rename K2 into KEEP
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | |- SRr _ _ {| cfg_ms := _; cfg_model := ?m |} _ => let x := fresh "mdv" in set (x := m) in *; clearbody x
  end.

Theorem c0tn : forall POST i, lx_from B MT POST (C0_N B MT i) -> lx_from B MT POST (LI_T B MT 0 i).
Proof.
  intros POST i HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HT.
  destruct HT as (pos & r & fab & op & bs & HBD & Hi & Hk & Hacc & Hblk & Hreg & Hinv & Hfab & Hprev & Hpos & Hop
                  & Hop3 & Hcur & Hsl & H19 & H20 & H21 & H23 & H24 & H26 & H27).
  assert (Hnb : exists nb : nat, ((nb = 0 /\ length (lc_pl cx) = S pos) \/ (nb = 1 /\ length (lc_pl cx) = S (S pos)) \/
                (nb = 2 /\ S (S pos) < length (lc_pl cx)))%nat).
  { destruct Hcur as (HL & _).
    destruct (Nat.eq_dec (length (lc_pl cx)) (S pos)) as [E0|N0]; [exists 0%nat; left; split; [reflexivity | exact E0]|].
    destruct (Nat.eq_dec (length (lc_pl cx)) (S (S pos))) as [E1|N1];
      [exists 1%nat; right; left; split; [reflexivity | exact E1]|].
    exists 2%nat. right; right. split; [reflexivity | lia]. }
  destruct Hnb as (nb & Hnb).
  pose proof (c0tn_seat cx fp k ly3 S3 W3 ms3 md3 pos r fab nb HB HJ HFR HBD Hblk Hcur Hsl H19 H20 H21 H27 Hnb)
    as HSEAT.
  set (E := lx_env cx fp (ms_regs ms3) (c0tn_ex cx fp r pos)) in *.
  assert (HEI : img_env VAL A_LIM E) by apply lx_env_img.
  pose proof HBD as (_ & _ & _ & _ & _ & _ & HREGS & _).
  assert (HE : lx_E cx fp E) by (apply (lx_env_E cx fp ms3 _); exact HREGS).
  pose proof (lx_extents B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR E HE) as (U8 & U2 & U46 & U22).
  pose proof (lx_sp_facts B MT cx HB) as (Hsp16 & Hsp0lo & Hsp0hi & Hsp1 & Hsp32).
  pose proof (lx_F_facts B MT LAWS cx fp W3 ms3 ly3 S3 md3 k HB HJ HFR) as (HF0 & HFc & HFia & HFo & HF64 & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  cbn [YP09.base_val] in U8, U2, U46, U22. unfold LA_SP in U2.
  pose proof HE as (HE2 & HE8 & HE3 & HE4 & HE22 & HE32 & _ & HE46 & _).
  assert (Hop256 : 0 <= op < 256) by
    (rewrite Hop; pose proof (bv_unsigned_in_range 8 (nth pos (lc_pl cx) (Z_to_bv 8 0))) as Q;
     change (bv_modulus 8) with 256 in Q; exact Q).
  assert (DEN : forall (x : sv) (v : Z), U E x = v -> sv_denot E x = Z_to_bv 64 v)
    by (intros x v Hx; rewrite <- Hx; unfold U; symmetry; apply Z_to_bv_bv_unsigned).
  assert (EW23 : ew E 23 = w64 op)
    by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) _ 23 (Z_to_bv 5 23)) by (vm_compute; reflexivity); exact H23).
  assert (E20 : ew E 20 = w64 r)
    by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) _ 20 (Z_to_bv 5 20)) by (vm_compute; reflexivity); exact H20).
  assert (E24 : ew E 24 = w64 (Z.of_nat i))
    by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) _ 24 (Z_to_bv 5 24)) by (vm_compute; reflexivity); exact H24).
  assert (E26 : ew E 26 = w64 (Boxreg.bx_n bs))
    by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) _ 26 (Z_to_bv 5 26)) by (vm_compute; reflexivity); exact H26).
  assert (E27 : ew E 27 = w64 fab)
    by (unfold E; rewrite (lx_env_reg cx fp (ms_regs ms3) _ 27 (Z_to_bv 5 27)) by (vm_compute; reflexivity); exact H27).
  assert (EX : forall j, (j < 7)%nat -> ew E (LA_EX + j) = nth j (c0tn_ex cx fp r pos) (w64 0))
    by (intros j Hj; apply lx_env_ex; lia).
  pose proof (EX 0%nat ltac:(lia)) as E48. pose proof (EX 1%nat ltac:(lia)) as E49.
  pose proof (EX 2%nat ltac:(lia)) as E50. pose proof (EX 3%nat ltac:(lia)) as E51.
  pose proof (EX 4%nat ltac:(lia)) as E52. pose proof (EX 5%nat ltac:(lia)) as E53.
  pose proof (EX 6%nat ltac:(lia)) as E54.
  cbn [nth c0tn_ex LA_EX Nat.add] in E48, E49, E50, E51, E52, E53, E54.
  clear EX.
  assert (U23 : U E (SOff 23 0) = op) by (apply (U_atom E 23 op EW23); lia).
  assert (UAND : U E (SAlu ALU_AND (SOff 23 0) (SLit 3)) = 0)
    by (rewrite U_and_lit by lia; rewrite U23; exact Hop3).
  assert (U1 : U E (SLit 1) = 1) by (apply U_lit; lia).
  (* ranges of the slot values at T *)
  pose proof Hsl as (S08 & S28 & S30 & S38 & S40 & S68 & S70 & S78).
  pose proof (c0_rdword_range _ _ _ _ S28) as Q28. pose proof (c0_rdword_range _ _ _ _ S30) as Q30.
  pose proof (c0_rdword_range _ _ _ _ S40) as Q40. pose proof (c0_rdword_range _ _ _ _ S70) as Q70.
  pose proof (c0_rdword_range _ _ _ _ S78) as Q78.
  assert (Hn5 : 0 <= Boxreg.bx_n bs <= 5) by (pose proof Hinv as ((_ & HB1 & _) & _); exact HB1).
  pose proof Hcur as (HcurL & Hcur88 & Hcur90).
  pose proof (c0_rdword_range _ _ _ _ Hcur88) as Q88.
  assert (Hpos1 : Z.of_nat (c0_pos1 (lc_pl cx) pos) =
                  Z.of_nat (S pos) + Z.min (Z.of_nat (length (lc_pl cx)) - Z.of_nat (S pos)) 2).
  { assert (Hu : LLVMFuzzerTestOneInput_case0.c0_used (c0_pl0 (lc_pl cx) pos) =
                 Z.min (Z.of_nat (length (lc_pl cx)) - Z.of_nat (S pos)) 2)
      by (unfold LLVMFuzzerTestOneInput_case0.c0_used, c0_pl0; rewrite length_skipn; lia).
    unfold c0_pos1. rewrite Nat2Z.inj_add, Z2Nat.id by (rewrite Hu; lia). rewrite Hu. reflexivity. }
  pose proof HJ as (HAR3 & _).
  pose proof HB as (_ & _ & _ & Hpn & _).
  assert (Hpin : In (lc_p cx, lc_n cx) (ablocks B (lc_ly cx) (lc_S cx)))
    by (destruct Hpn as [Hn0 | Hn]; [unfold lc_n in Hn0; lia | exact (proj2 Hn)]).
  assert (Hpin3 : In (lc_p cx, lc_n cx) (ablocks B ly3 S3))
    by (unfold lblk in Hblk; rewrite Hblk; apply in_or_app; left; exact Hpin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hpin3) as (_ & Hp4096 & Hpceil & _).
  assert (Hreq : req_size (lc_n cx) = lc_n cx)
    by (unfold req_size; rewrite (proj2 (Z.eqb_neq (lc_n cx) 0)) by (unfold lc_n; lia); reflexivity).
  rewrite Hreq in Hpceil.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (lsp1 cx <= a < lsp1 cx + 152) ->
    aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by reflexivity.
  destruct Hnb as [(-> & HL) | [(-> & HL) | (-> & HL)]]; destruct HSEAT as [HS SHOK].
  (* 0x8034c .. 0x80354 blt s3, a0 (s3 = 1, a0 = op & 3 = 0: not taken) *)
  all: paj_run_tok RUN HS HJ SHOK c0tn_Bspan; [c0tn_awr2 U2 (lsp1 cx - lsp0 cx) |]; c0tn_after U2 cx KEEP.
  all: psrr_branch_tok RUN BR HS SHOK c0tn_Bspan;
    [ exfalso; rewrite (DEN _ _ U1), (DEN _ _ UAND) in Hc; cbn [branch_taken] in Hc;
      rewrite bv_lts_small in Hc by lia; discriminate | clear Hc ].
  (* .. 0x8035c bnez a0 (a0 = 0: not taken) *)
  all: paj_run_tok RUN HS HJ SHOK c0tn_Bspan; [c0tn_awr2 U2 (lsp1 cx - lsp0 cx) |]; c0tn_after U2 cx KEEP.
  all: psrr_branch_tok RUN BR HS SHOK c0tn_Bspan;
    [ exfalso; rewrite branch_ne_U, UAND, (U_lit E 0 ltac:(lia)) in Hc; discriminate | clear Hc ].
  (* nb = 0: to the first `beqz a1` (0x80364); nb = 1: to the second (0x80398); nb = 2: to the call *)
  all: paj_run_tok RUN HS HJ SHOK c0tn_Bspan; [c0tn_awr2 U2 (lsp1 cx - lsp0 cx) |]; c0tn_after U2 cx KEEP.
  - (* nb = 0: no byte left, beqz a1 taken (a1 = 0) to 0x80508 *)
    assert (U49 : U E (SOff 49 0) = 0).
    { apply (U_atom E 49 0); [|lia]. rewrite E49. unfold w64, lc_n. rewrite HL. f_equal. lia. }
    psrr_branch_tok RUN BR HS SHOK c0tn_Bspan;
      [ clear Hc | exfalso; rewrite branch_eq_U, U49, (U_lit E 0 ltac:(lia)) in Hc; cbn in Hc; discriminate ].
    all: try (unfold lc_n; rewrite HL; lia).
    paj_run_tok RUN HS HJ SHOK c0tn_Bspan; [c0tn_awr2 U2 (lsp1 cx - lsp0 cx) |]; c0tn_after U2 cx KEEP.

    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (EQX : forall n, (n < 512)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
    end.
    assert (U2x : bv_unsigned (ew _ 2) = lsp1 cx) by (rewrite ?EQX by lia; exact U2).
    pmkst HS.
    lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
      let rg := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (st_ok_region_nth Ex ss _ 1 rg HS ltac:(vm_compute; reflexivity)) as HR1
    end.
    cbn [restrict ms_mem] in HR1.
    lazymatch type of HR1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
      assert (SL : forall off e v, In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot Ex e = w64 v -> 0 <= v < 2 ^ 64 ->
                lslot cx W3 msC off v)
        by (intros off e v Hin He Hv; unfold lslot, lview;
            apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msC)); [|exact Hv];
            exact (c0tn_slot_of Ex _ cs lo hi wlo whi off e v (lsp1 cx) HR1 U2x Hin He Hv))
    end.
    apply (c0tn_call POST i cx fp k acc ly3 S3 W3 ms3 msC _ pos r fab op bs HN HB HJ HFR HMO HBD Hi Hk Hacc Hblk Hreg Hinv
             Hfab Hprev Hpos Hop Hop3 KEEP).
    + split; [apply (c0tn_reg _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE8]|].
      split; [apply (c0tn_reg _ _ _ _ 9%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 3%bv (SOff 3 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE3]|].
      split; [apply (c0tn_reg _ _ _ _ 4%bv (SOff 4 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE4]|].
      split; [apply (c0tn_reg _ _ _ _ 18%bv (SOff 32 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE32]|].
      apply (c0tn_reg _ _ _ _ 22%bv (SOff 22 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE22].
    + apply (c0tn_reg _ _ _ _ 1%bv (SOff 240 1400) _ HS); [vm_compute; reflexivity|].
      cbn [sv_denot]. rewrite ?EQX by lia. rewrite (img_env_codeptr E HEI). reflexivity.
    + apply (c0tn_reg _ _ _ _ 10%bv (SOff 2 136) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE2 | lia].
    + apply (c0tn_reg _ _ _ _ 20%bv (SOff 20 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E20].
    + apply (c0tn_reg _ _ _ _ 21%bv (SOff 46 64) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia].
    + apply (c0tn_reg _ _ _ _ 23%bv (SOff 23 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact EW23].
    + apply (c0tn_reg _ _ _ _ 25%bv (SLit 0) _ HS); [vm_compute; reflexivity|].
      rewrite (proj1 (c0tn_vals0 _ _ HL)). reflexivity.
    + apply (c0tn_reg _ _ _ _ 26%bv (SLit 0) _ HS); [vm_compute; reflexivity|].
      rewrite (proj2 (c0tn_vals0 _ _ HL)). reflexivity.
    + apply (c0tn_reg _ _ _ _ 27%bv (SOff 27 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E27].
    + split; [apply (SL 0x08 (SLit 3)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x28 (SOff 20 280)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact E20 | lia] | lia]|].
      split; [apply (SL 0x30 (SOff 27 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E27 | lia]|].
      split; [apply (SL 0x38 (SLit 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x40 (SOff 52 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E52 | lia]|].
      split; [apply (SL 0x68 (SOff 46 32)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia] | lia]|].
      split; [apply (SL 0x70 (SOff 53 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E53 | lia]|].
      apply (SL 0x78 (SOff 54 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E54 | lia].
    + apply (SL 0x10 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x18 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x80 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x48 (SOff 26 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E26 | lia].
    + rewrite (proj2 (c0tn_vals0 _ _ HL)). change ((0 * 2 ^ 56) mod 2 ^ 64) with 0.
      apply (SL 0x50 (SLit 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia].
    + apply (SL 0x58 (SOff 24 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E24 | lia].
    + split; [lia|].
      split.
      * apply (SL 0x88 (SOff 48 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil; lia].
        rewrite (c0tn_den_atom _ 48 (lc_p cx + Z.of_nat (S pos)) 0); [unfold w64; f_equal; lia | rewrite ?EQX by lia; exact E48 | lia].
      * apply (SL 0x90 (SOff 49 (-0))); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil |- *; lia].
        rewrite (c0tn_den_atom _ 49 (lc_n cx - Z.of_nat (S pos)) (-0));
          [unfold w64; f_equal; unfold lc_n; lia | rewrite ?EQX by lia; exact E49 | unfold lc_n in Hpceil |- *; lia].
  - (* nb = 1: one byte left (nch), the second beqz a1 taken (a1 = 0) to 0x8050c *)
    psrr_branch_tok RUN BR HS SHOK c0tn_Bspan.
    all: rewrite branch_eq_U, !U_SOff, (U_lit _ 0 ltac:(lia)) in Hc; rewrite !ew_ewset_other in Hc by lia.
    all: rewrite E49 in Hc; unfold w64, lc_n in Hc; rewrite HL, unsigned_lit_small in Hc by lia.
    all: replace (Z.of_nat (S (S pos)) - Z.of_nat (S pos) + -1) with 0 in Hc by lia; cbn in Hc.
    2: discriminate.
    clear Hc.
    paj_run_tok RUN HS HJ SHOK c0tn_Bspan; [c0tn_awr2 U2 (lsp1 cx - lsp0 cx) |]; c0tn_after U2 cx KEEP.

    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (EQX : forall n, (n < 512)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
    end.
    assert (U2x : bv_unsigned (ew _ 2) = lsp1 cx) by (rewrite ?EQX by lia; exact U2).
    pmkst HS.
    lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
      let rg := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (st_ok_region_nth Ex ss _ 1 rg HS ltac:(vm_compute; reflexivity)) as HR1
    end.
    cbn [restrict ms_mem] in HR1.
    lazymatch type of HR1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
      assert (SL : forall off e v, In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot Ex e = w64 v -> 0 <= v < 2 ^ 64 ->
                lslot cx W3 msC off v)
        by (intros off e v Hin He Hv; unfold lslot, lview;
            apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msC)); [|exact Hv];
            exact (c0tn_slot_of Ex _ cs lo hi wlo whi off e v (lsp1 cx) HR1 U2x Hin He Hv))
    end.
    apply (c0tn_call POST i cx fp k acc ly3 S3 W3 ms3 msC _ pos r fab op bs HN HB HJ HFR HMO HBD Hi Hk Hacc Hblk Hreg Hinv
             Hfab Hprev Hpos Hop Hop3 KEEP).
    + split; [apply (c0tn_reg _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE8]|].
      split; [apply (c0tn_reg _ _ _ _ 9%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 3%bv (SOff 3 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE3]|].
      split; [apply (c0tn_reg _ _ _ _ 4%bv (SOff 4 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE4]|].
      split; [apply (c0tn_reg _ _ _ _ 18%bv (SOff 32 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE32]|].
      apply (c0tn_reg _ _ _ _ 22%bv (SOff 22 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE22].
    + apply (c0tn_reg _ _ _ _ 1%bv (SOff 240 1400) _ HS); [vm_compute; reflexivity|].
      cbn [sv_denot]. rewrite ?EQX by lia. rewrite (img_env_codeptr E HEI). reflexivity.
    + apply (c0tn_reg _ _ _ _ 10%bv (SOff 2 136) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE2 | lia].
    + apply (c0tn_reg _ _ _ _ 20%bv (SOff 20 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E20].
    + apply (c0tn_reg _ _ _ _ 21%bv (SOff 46 64) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia].
    + apply (c0tn_reg _ _ _ _ 23%bv (SOff 23 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact EW23].
    + apply (c0tn_reg _ _ _ _ 25%bv (SOff 50 0) _ HS); [vm_compute; reflexivity|].
      rewrite (c0tn_vals1 (lc_pl cx) pos) by lia. rewrite lx_sv_SOff0, ?EQX by lia. exact E50.
    + apply (c0tn_reg _ _ _ _ 26%bv (SLit 0) _ HS); [vm_compute; reflexivity|].
      rewrite (c0tn_vals1b _ _ HL). reflexivity.
    + apply (c0tn_reg _ _ _ _ 27%bv (SOff 27 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E27].
    + split; [apply (SL 0x08 (SLit 3)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x28 (SOff 20 280)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact E20 | lia] | lia]|].
      split; [apply (SL 0x30 (SOff 27 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E27 | lia]|].
      split; [apply (SL 0x38 (SLit 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x40 (SOff 52 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E52 | lia]|].
      split; [apply (SL 0x68 (SOff 46 32)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia] | lia]|].
      split; [apply (SL 0x70 (SOff 53 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E53 | lia]|].
      apply (SL 0x78 (SOff 54 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E54 | lia].
    + apply (SL 0x10 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x18 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x80 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x48 (SOff 26 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E26 | lia].
    + rewrite (c0tn_vals1b _ _ HL). change ((0 * 2 ^ 56) mod 2 ^ 64) with 0.
      apply (SL 0x50 (SLit 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia].
    + apply (SL 0x58 (SOff 24 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E24 | lia].
    + split; [lia|].
      split.
      * apply (SL 0x88 (SOff 48 1)); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil; lia].
        rewrite (c0tn_den_atom _ 48 (lc_p cx + Z.of_nat (S pos)) 1); [unfold w64; f_equal; lia | rewrite ?EQX by lia; exact E48 | lia].
      * apply (SL 0x90 (SOff 49 (-1))); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil |- *; lia].
        rewrite (c0tn_den_atom _ 49 (lc_n cx - Z.of_nat (S pos)) (-1));
          [unfold w64; f_equal; unfold lc_n; lia | rewrite ?EQX by lia; exact E49 | unfold lc_n in Hpceil |- *; lia].
  - (* nb = 2: at the call *)

    lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
    lazymatch type of HS with st_ok _ ?Ex _ _ =>
      assert (EQX : forall n, (n < 512)%nat -> ew Ex n = ew E n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
    end.
    assert (U2x : bv_unsigned (ew _ 2) = lsp1 cx) by (rewrite ?EQX by lia; exact U2).
    pmkst HS.
    lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
      let rg := eval vm_compute in (nth 1 (ss_mem ss) (YP09.mkRegion None 0 0 0 0 [])) in
      pose proof (st_ok_region_nth Ex ss _ 1 rg HS ltac:(vm_compute; reflexivity)) as HR1
    end.
    cbn [restrict ms_mem] in HR1.
    lazymatch type of HR1 with region_ok _ ?Ex _ (YP09.mkRegion (Some 2%nat) ?lo ?hi ?wlo ?whi ?cs) =>
      assert (SL : forall off e v, In (YP09.mkChunk off (CVal 8 e)) cs -> sv_denot Ex e = w64 v -> 0 <= v < 2 ^ 64 ->
                lslot cx W3 msC off v)
        by (intros off e v Hin He Hv; unfold lslot, lview;
            apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msC)); [|exact Hv];
            exact (c0tn_slot_of Ex _ cs lo hi wlo whi off e v (lsp1 cx) HR1 U2x Hin He Hv))
    end.
    apply (c0tn_call POST i cx fp k acc ly3 S3 W3 ms3 msC _ pos r fab op bs HN HB HJ HFR HMO HBD Hi Hk Hacc Hblk Hreg Hinv
             Hfab Hprev Hpos Hop Hop3 KEEP).
    + split; [apply (c0tn_reg _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE8]|].
      split; [apply (c0tn_reg _ _ _ _ 9%bv (SOff 2 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE2]|].
      split; [apply (c0tn_reg _ _ _ _ 3%bv (SOff 3 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE3]|].
      split; [apply (c0tn_reg _ _ _ _ 4%bv (SOff 4 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE4]|].
      split; [apply (c0tn_reg _ _ _ _ 18%bv (SOff 32 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE32]|].
      apply (c0tn_reg _ _ _ _ 22%bv (SOff 22 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact HE22].
    + apply (c0tn_reg _ _ _ _ 1%bv (SOff 240 1400) _ HS); [vm_compute; reflexivity|].
      cbn [sv_denot]. rewrite ?EQX by lia. rewrite (img_env_codeptr E HEI). reflexivity.
    + apply (c0tn_reg _ _ _ _ 10%bv (SOff 2 136) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE2 | lia].
    + apply (c0tn_reg _ _ _ _ 20%bv (SOff 20 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E20].
    + apply (c0tn_reg _ _ _ _ 21%bv (SOff 46 64) _ HS); [vm_compute; reflexivity|].
      apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia].
    + apply (c0tn_reg _ _ _ _ 23%bv (SOff 23 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact EW23].
    + apply (c0tn_reg _ _ _ _ 25%bv (SOff 50 0) _ HS); [vm_compute; reflexivity|].
      rewrite (c0tn_vals1 (lc_pl cx) pos) by lia. rewrite lx_sv_SOff0, ?EQX by lia. exact E50.
    + apply (c0tn_reg _ _ _ _ 26%bv (SAlu ALU_SRA (SAlu ALU_SLL (SOff 51 0) (SLit 56)) (SLit 56)) _ HS);
        [vm_compute; reflexivity|].
      rewrite (c0tn_vals2 _ _ HL). apply c0tn_sext. rewrite ?EQX by lia. exact E51.
    + apply (c0tn_reg _ _ _ _ 27%bv (SOff 27 0) _ HS); [vm_compute; reflexivity | rewrite lx_sv_SOff0, ?EQX by lia; exact E27].
    + split; [apply (SL 0x08 (SLit 3)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x28 (SOff 20 280)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact E20 | lia] | lia]|].
      split; [apply (SL 0x30 (SOff 27 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E27 | lia]|].
      split; [apply (SL 0x38 (SLit 0)); [cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | lia]|].
      split; [apply (SL 0x40 (SOff 52 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E52 | lia]|].
      split; [apply (SL 0x68 (SOff 46 32)); [cbn [In]; repeat (first [left; reflexivity | right])
                | apply c0tn_den_atom; [rewrite ?EQX by lia; exact HE46 | lia] | lia]|].
      split; [apply (SL 0x70 (SOff 53 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E53 | lia]|].
      apply (SL 0x78 (SOff 54 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E54 | lia].
    + apply (SL 0x10 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x18 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x80 (SOff 46 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact HE46 | lia].
    + apply (SL 0x48 (SOff 26 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E26 | lia].
    + rewrite (c0tn_vals2 _ _ HL).
      apply (SL 0x50 (SAlu ALU_SLL (SOff 51 0) (SLit 56)));
        [cbn [In]; repeat (first [left; reflexivity | right]) | apply c0tn_shl; rewrite ?EQX by lia; exact E51
        | apply Z.mod_pos_bound; lia].
    + apply (SL 0x58 (SOff 24 0)); [cbn [In]; repeat (first [left; reflexivity | right])
                | rewrite lx_sv_SOff0, ?EQX by lia; exact E24 | lia].
    + split; [lia|].
      split.
      * apply (SL 0x88 (SOff 48 2)); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil; lia].
        rewrite (c0tn_den_atom _ 48 (lc_p cx + Z.of_nat (S pos)) 2); [unfold w64; f_equal; lia | rewrite ?EQX by lia; exact E48 | lia].
      * apply (SL 0x90 (SOff 49 (-2))); [cbn [In]; repeat (first [left; reflexivity | right]) | | unfold lc_n in Hpceil |- *; lia].
        rewrite (c0tn_den_atom _ 49 (lc_n cx - Z.of_nat (S pos)) (-2));
          [unfold w64; f_equal; unfold lc_n; lia | rewrite ?EQX by lia; exact E49 | unfold lc_n in Hpceil |- *; lia].
Qed.

End a.
