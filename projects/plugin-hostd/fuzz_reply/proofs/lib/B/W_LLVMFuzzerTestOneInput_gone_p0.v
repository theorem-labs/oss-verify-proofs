(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B,
   PHASE p0 (lib/B/W_LLVMFuzzerTestOneInput_gone.v's GP0): the arm's entry 0x849a0 to the join 0x84aa8
   (fuzz_reply.asan-ubsan, fuzz_reply.c:718-720 `op_gone(fuzz_u8(&in))`), the image-B twin of
   lib/A/W_LLVMFuzzerTestOneInput_gone_p0.v (a working branch 32b23a20c3e), read from B's objdump:
     0x849a0  sd   s9,88(s1)          t to F+88 (s9 is rewritten by the reads[] loop; reloaded at 0x84da4)
     0x849a4  beqz t1,84a9c           t1 = in.n left after the op byte
   in.n = 0:  0x84a9c sd zero,144(s1); li s5,0; sd s4,16(s1)      (fuzz_u8 gives 0 and consumes nothing)
   in.n > 0:  0x849a8 addi a2,s4,1; 0x849ac bgeu s7,a2,850fc (the UBSan PTR_INC trap: s7 = 1, a2 = cursor + 1 > 1,
              decided by the atom facts of s7 and s4); 0x849b0-0x849bc the shadow check of the byte at s4 (inside the
              live input block, so the slow path 0x84e30 and the report 0x8517c are not reached); 0x849c0 sd a2,16(s1);
              lbu s5,0(s4); addi t1,t1,-1; sd t1,144(s1); j 84aa8.
   The entry state carries three narrow frame windows (F+16, F+88, F+144), so the run's frame_of keeps every other
   frame byte; the cut's facts are carried across the stores with the arm's transport kit
   (W_LLVMFuzzerTestOneInput_gone_tk.v).  The model m at the join is INV_A's own model. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_gone_base W_LLVMFuzzerTestOneInput_gone_tk.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the entry state at 0x849a0 *)
(* the frame windows F+16 (in.p), F+88 (t), F+144 (in.n), all written; for in.n > 0 also the byte at the cursor s4
   (atom 20), read into atom 32 *)
Definition gp0_frA : YP09.region := YP09.mkRegion (Some 9%nat) 16 24 16 24 [].
Definition gp0_frT : YP09.region := YP09.mkRegion (Some 9%nat) 88 96 88 96 [].
Definition gp0_frB : YP09.region := YP09.mkRegion (Some 9%nat) 144 152 144 152 [].
Definition gp0_inA : YP09.region := YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition gp0_reg (more : bool) : smem :=
  if more then [gp0_frA; gp0_frT; gp0_frB; gp0_inA] else [gp0_frA; gp0_frT; gp0_frB].
(* s1 = F (32-aligned), s4 = the cursor (a user address), s7 = 1 (decides the PTR_INC trap), s11 = SB, the byte *)
Definition gp0_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF 1 1 0);
           (27%nat, mkAF SB SB 0); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_gp0 (more : bool) : sstate := mkSS AF_arm_gone sr_atoms (gp0_reg more) None gp0_facts.
(* the shadow entry of the token run: the byte at the cursor, inside the live input block *)
Definition gp0_SH (more : bool) : list shent := if more then [mkSHE 20 0 1] else [].
Definition gp0_extra (idv : Z) : list word := map (Z_to_bv 64) [idv].
Definition gp0_Bx : sv := SOff 27 0.
Definition gp0_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers neither path writes (a0, a1, a2, s5 and t1 move) *)
Definition GP0_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 25; 26; 27]%bv.

(* a run's write obligation: the three windows are in the function's own stack window, the input region is
   read-only *)
Local Ltac gp0_awr U9 :=
  cbn [ss_mem add_cond ss_gp0 gp0_reg];
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [gp0_frA gp0_frT gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      rewrite ?ew_ewset_other in Ha by lia; rewrite ?U9 in Ha;
      first [ lia | left; split; [left; unfold YCfn.LLVMF_STK in *; lia | lia] ]
    | ]);
  apply awr_ok_x_nil.
(* a byte outside the three windows is outside every region's writable window *)
Local Ltac gp0_nowr U9 Hna Hnt Hnb :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gp0 gp0_reg In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [gp0_frA gp0_frT gp0_frB gp0_inA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; rewrite ?U9 in Hr; lia | ]);
  destruct Hin.

Section gp0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* errno's place, the base's GN_ERRNO_LOW: the transport of aout_at across the three stores reads it *)
Hypothesis HERR : GN_ERRNO_LOW B.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
Let RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

Lemma gp0_entry : forall (W : world segs) ly S mem md regs (more : bool) idv F tv,
  AR segs B ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 20 = w64 tv -> getr regs 23 = w64 1 -> getr regs 27 = w64 SB ->
  2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 216 ->
  4096 <= tv <= 140737479966720 -> tv + 1 <= F -> 0 <= idv < 256 ->
  (more = true -> val_mem segs (arm W mem) tv 1 idv /\
     exists p n, In (p, n) (ablocks B ly S) /\ p <= tv /\ tv + 1 <= p + req_size n) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gp0_extra idv))) (ss_gp0 more)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_gone)) mem (seg_rom segs)))
  /\ sh_ok segs gp0_Bx (gp0_SH more) (Eimg (Ereg regs (gp0_extra idv))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S mem md regs more idv F tv HAR R9 R20 R23 R27 HF1 HF2 HF3 HFw Ht1 Ht2 Hid Hmore.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gp0_extra idv))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew E 20) = tv) by (rewrite (EE 20%nat 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = 1) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
  assert (U27 : bv_unsigned (ew E 27) = SB) by (rewrite (EE 27%nat 27%bv eq_refl), R27; apply unsigned_lit_small; unfold SB; lia).
  assert (U32 : bv_unsigned (ew E 32) = idv) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gp0. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + destruct more; vm_compute; reflexivity.
    + assert (RA : region_ok segs E (mrestrict (w_H W) mem) gp0_frA).
      { unfold region_ok, gp0_frA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      assert (RT : region_ok segs E (mrestrict (w_H W) mem) gp0_frT).
      { unfold region_ok, gp0_frT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      assert (RB : region_ok segs E (mrestrict (w_H W) mem) gp0_frB).
      { unfold region_ok, gp0_frB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; apply HFw; lia|]. constructor. }
      destruct more; [|constructor; [exact RA | constructor; [exact RT | constructor; [exact RB | constructor]]]].
      destruct (Hmore eq_refl) as (Hv & _).
      constructor; [exact RA|]. constructor; [exact RT|]. constructor; [exact RB|]. constructor; [|constructor].
      unfold region_ok, gp0_inA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ tv 0 1 (SOff 32 0) idv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hv].
    + apply pairwise_disjoint_of_extents. destruct more; unfold gp0_reg, gp0_frA, gp0_frT, gp0_frB, gp0_inA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U20;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [gp0_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U20, U23, U27, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, gp0_SH; [|constructor].
    destruct (Hmore eq_refl) as (_ & p & n & Hin & Hp1 & Hp2).
    constructor; [|constructor].
    apply (gn_shent_in_block B LAWS ly S W mem md E gp0_Bx 20 tv p n 0 1 HAR Hin); try lia.
    + unfold gp0_Bx, U. cbn [sv_denot]. rewrite U27, Z.add_0_r, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.

(* one input byte, as the program reads it (A's p0 gp0_byte, verbatim) *)
Lemma gp0_byte : forall cx ly3 S3 (W : world segs) mem j,
  c_n cx = Z.of_nat (length (c_pl cx)) ->
  ainput_at B cx ly3 S3 W mem -> 0 <= j < c_n cx ->
  val_mem segs (mrestrict (w_H W) mem) (c_p cx + j) 1 (in_byte cx j).
Proof.
  intros cx ly3 S3 W mem j Hlen HAI Hj. destruct HAI as (_ & Hg). unfold arm in Hg.
  assert (Hjn : (Z.to_nat j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat)
    by (rewrite length_map; rewrite <- Nat2Z.id; apply Z2Nat.inj_lt; lia).
  destruct (Hg (Z.to_nat j) Hjn) as (Hv & _).
  rewrite Z2Nat.id in Hv by lia.
  replace (nth (Z.to_nat j) (map (fun b : byte => bv_unsigned b) (c_pl cx)) 0)
    with (in_byte cx j) in Hv; [exact Hv|].
  unfold in_byte. rewrite (nth_indep (map _ (c_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hjn.
  rewrite List.map_nth. reflexivity.
Qed.
Lemma gp0_in_byte_rng : forall cx j, 0 <= in_byte cx j < 256.
Proof. intros cx j. unfold in_byte. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat j) (c_pl cx) (Z_to_bv 8 0))) as H. exact H. Qed.

(* a byte present before a run that only grows the memory is present after it *)
Lemma gp0_pres_grows : forall (W : world segs) m m' a,
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
  intros W m m' a HGr [Hh [b Hb]]. split; [exact Hh|].
  specialize (HGr (Z_to_bv 64 a)). unfold mrestrict in HGr. rewrite Hh in HGr.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
  exfalso. apply HGr; [rewrite Hb; discriminate | reflexivity].
Qed.

(* B's frame (aframe_at: no `full` flag) across a run whose only stores are the cells F+16, F+88 and F+144 *)
Lemma gp0_aframe_kept : forall cx FF (W W' : world segs) mem mem',
  aframe_at cx FF W mem ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 16 <= a < lf_F cx + 24) -> ~ (lf_F cx + 88 <= a < lf_F cx + 96) ->
     ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W' mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W' mem') a) ->
  GK_CEIL8 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  0 <= FF -> FF + 128 <= GK_CEIL8 -> 0 <= SB + FF / 8 -> SB + FF / 8 + 16 <= GK_CEIL8 ->
  aframe_at cx FF W' mem'.
Proof.
  intros cx FF W W' mem mem'
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20
     & A21 & A22) HK WK HLO HF1 HF2 HFF0 HFF1 HS0 HS1.
  pose proof gk_ceil_lo as HCL. unfold GK_CEIL8 in *.
  assert (KW : forall a n, awr W mem a n -> awr W' mem' a n) by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lf_F cx + 16 \/ lf_F cx + 24 <= a) ->
             (a + 8 <= lf_F cx + 88 \/ lf_F cx + 96 <= a) ->
             (a + 8 <= lf_F cx + 144 \/ lf_F cx + 152 <= a) -> sv8 W mem a v -> sv8 W' mem' a v).
  { intros a v H0 H1 H2 H3 H4 Hv. apply (gk_sv8_kept W W' mem mem'); [|exact Hv]. intros x Hx. apply HK; lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | lia | lia | lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  do 17 (split; [apply KV; [lia | lia | lia | lia | lia | assumption]|]).
  split; [exact (KW _ _ A20)|].
  split; [|exact (KW _ _ A22)].
  apply (akept_garr8 W mem); [|exact A21]. intros x Hx.
  unfold fake_shadow in Hx. cbn [length] in Hx. apply HK; lia.
Qed.

(* the registers the join keeps from the dispatch, from the ones neither path writes *)
Lemma gp0_kregs : forall cx FF (regsD regs' : bvmap 5 word),
  (forall r, In r GP0_KEPT -> getr regs' r = getr regsD r) ->
  lregs_common B cx FF regsD ->
  gn_kregs B cx FF regs' /\ getr regs' 24 = w64 (SB + FF / 8) /\ getr regs' 26 = w64 HI_G_NOUT.
Proof.
  intros cx FF regsD regs' KK (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  unfold gn_kregs.
  rewrite !KK by (cbv; tauto).
  repeat split; assumption.
Qed.

(* the join's predicate from the entry's cut facts, carried across the three stores *)
Lemma gp0_close : forall cx t m (W : world segs) mem mem' md md' regs' ly3 S3 k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  AR segs B ly3 S3 W mem md ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem' md' k ->
  aframe_at cx (frame_addr ly3 1 fpos) W mem ->
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) ->
  amodel_at B ly3 S3 W mem m ->
  ainput_at B cx ly3 S3 W mem -> rom_view segs W mem -> jt_rom W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx t m ly3 S3 -> RINV cx t m -> gn_op cx t m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lf_F cx + 16 <= a < lf_F cx + 24) -> ~ (lf_F cx + 88 <= a < lf_F cx + 96) ->
     ~ (lf_F cx + 144 <= a < lf_F cx + 152) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  sv8 W mem' (lf_F cx + 16) (c_p cx + gn_kq cx m) -> sv8 W mem' (lf_F cx + 144) (c_n cx - gn_kq cx m) ->
  sv8 W mem' (lf_F cx + 88) t ->
  gn_kregs B cx (frame_addr ly3 1 fpos) regs' ->
  getr regs' 24 = w64 (SB + frame_addr ly3 1 fpos / 8) -> getr regs' 26 = w64 HI_G_NOUT ->
  getr regs' 21 = w64 (gn_id cx m) ->
  GJN B G_fr fr_FP LS RINV cx t m W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_join)) mem' (seg_rom segs)) md').
Proof.
  intros cx t m W mem mem' md md' regs' ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HJT HSEP HLS HRI HOP KEEP WK
    SV16 SV144 SV88 KR R24 R26 R21.
  destruct (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly3 S3 W mem' md' k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR').
  pose proof HB as (_ & HPRE). pose proof HPRE as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof gk_ceil_lo as HCL. pose proof HERR as (HE0 & HE1).
  assert (FF8 : 0 <= frame_addr ly3 1 fpos / 8 /\ 8 * (frame_addr ly3 1 fpos / 8) <= frame_addr ly3 1 fpos)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  assert (KL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem' a)
    by (intros a Ha; apply KEEP; unfold GK_CEIL8, YCfn.LLVMF_STK in *; lia).
  unfold GJN. exists regs', mem', md', ly3, S3, k, fpos.
  split; [reflexivity|].
  split.
  { unfold gcom. split; [exact HJ|].
    split.
    { apply gframe_of_aframe. apply (gp0_aframe_kept cx _ W W mem mem' HFR KEEP WK);
        unfold GK_CEIL8, SB, YCfn.LLVMF_STK in *; lia. }
    split.
    { apply (gk_sv8_kept W W mem mem'); [|exact HFL]. intros x Hx. apply KL.
      unfold GK_CEIL8 in *. lia. }
    split; [exact SV16|]. split; [exact SV144|]. split; [exact SV88|].
    split; [exact (gk_ainput_kept B LAWS cx ly3 S3 W mem md W mem' HAR HIN (eq_sym Hnlen) KL)|].
    split; [exact (gk_rom_kept W W mem mem' HRV KL)|].
    exact (gk_jt_kept W W mem mem' HJT KL). }
  split; [exact (gk_amodel_kept B LAWS ly3 S3 W mem md W mem' m HAR HMOD HE0 HE1 KL)|].
  split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|].
  split; [exact KR|]. split; [exact R24|]. split; [exact R26 | exact R21].
Qed.

(* ------------------------------------------------------------------ GP0: the entry 0x849a0 to the join 0x84aa8 *)
Lemma gp0_entry_join : forall cx t W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> INV_A B G_fr fr_FP LS RINV 5 cx t W c ->
  SRr segs W c (fun W' c' => exists m, GJN B G_fr fr_FP LS RINV cx t m W' c').
Proof.
  intros cx t W c HB (regs & regsD & mem & md & -> & KR0 & HD11 & HJOUR & HROM & HLF).
  destruct HLF as (own & ly3 & S3 & k & m & fpos & HJ & Hown & HFR & HFL & HMOD & HIN & HRV & HSEP & HLS & HRI & HR).
  subst own.
  unfold lregs_D in HR. cbv zeta in HR.
  destruct HR as (HCOM & R25 & Ht & Hk & HO & R11 & HPK).
  pose proof HCOM as (C2 & C8 & C9 & C18 & C19 & C23 & C24 & C26 & C27 & C3 & C4).
  (* the operation is 5: not a picking one, so s4 = in.p + k + 1, t1 = in.n - k - 1 (the cursor after the op byte) *)
  assert (Hop : in_byte cx (lm_k m) mod 10 = 5).
  { pose proof (Z.mod_pos_bound (in_byte cx (lm_k m)) 10 ltac:(lia)) as Hb.
    rewrite HD11 in R11. apply (f_equal bv_unsigned) in R11. unfold w64 in R11.
    rewrite !unsigned_lit_small in R11 by lia. lia. }
  rewrite Hop in HPK. change (picks 5) with false in HPK. cbv iota in HPK.
  destruct HPK as (R20 & R6 & R21).
  assert (HOP : gn_op cx t m) by (split; [exact Hop | split; [exact HO | split; [exact Ht | exact Hk]]]).
  destruct (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly3 S3 W mem md k fpos HB HJ eq_refl)
    as (Hal & Hsp & HF32 & HFb & HFF4 & HFFc & HFFa & Hfrs & HAR).
  pose proof HB as (HAI0 & HPRE).
  pose proof HPRE as (HFNP & _ & _ & _ & Hnrng & Hnlen & _).
  pose proof HIN as [[(Hn0 & _) | (Hn & Hin)] HIG]; [lia|].
  destruct (al_blocks _ _ LAWS ly3 S3 W mem md (c_p cx) (c_n cx) HAR Hin) as (Hp16 & Hp4096 & Hpceil & Hph_ia & _ & _).
  pose proof (asan_consts) as (C1c & C2c & C3c & C4c & C5c).
  assert (Hreq : c_n cx <= req_size (c_n cx)) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  pose proof HFR as (HSV & HAWR & _).
  set (F := lf_F cx) in *. set (FF := frame_addr ly3 1 fpos) in *. set (sp0 := spZ (c_regs cx)) in *.
  set (tv := c_p cx + lm_k m + 1).
  assert (R9 : getr regs 9 = w64 F) by (rewrite (KR0 9%bv ltac:(cbv; tauto)); exact C9).
  assert (R27 : getr regs 27 = w64 SB) by (rewrite (KR0 27%bv ltac:(cbv; tauto)); exact C27).
  assert (R23 : getr regs 23 = w64 1) by (rewrite (KR0 23%bv ltac:(cbv; tauto)); exact C23).
  assert (R20' : getr regs 20 = w64 tv) by (rewrite (KR0 20%bv ltac:(cbv; tauto)); exact R20).
  assert (R6' : getr regs 6 = w64 (c_n cx - lm_k m - 1)) by (rewrite (KR0 6%bv ltac:(cbv; tauto)); exact R6).
  assert (R25' : getr regs 25 = w64 t) by (rewrite (KR0 25%bv ltac:(cbv; tauto)); exact R25).
  assert (P1 : 2 ^ 46 <= F) by (unfold YCfn.LLVMF_STK in *; lia).
  assert (P2 : F + 216 <= 2 ^ 47) by lia.
  assert (P3 : awr W mem F 216) by (intros o Ho; apply HAWR; lia).
  assert (P4 : 4096 <= tv <= 140737479966720) by (unfold tv; lia).
  assert (P5 : tv + 1 <= F) by (unfold tv, YCfn.LLVMF_STK in *; lia).
  assert (Ht64 : 0 <= t < 2 ^ 64) by (unfold OPS_MAX in Ht; lia).
  destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hmore | Hmore].
  - (* in.n > 0 after the op byte: the id is in.p[0] *)
    set (idv := in_byte cx (lm_k m + 1)).
    assert (P6 : true = true -> val_mem segs (arm W mem) tv 1 idv /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n).
    { intros _. split; [unfold tv, idv; replace (c_p cx + lm_k m + 1) with (c_p cx + (lm_k m + 1)) by lia;
        exact (gp0_byte cx ly3 S3 W mem (lm_k m + 1) Hnlen HIN ltac:(lia))|].
      exists (c_p cx), (c_n cx). split; [exact Hin|]. unfold tv. lia. }
    destruct (gp0_entry W ly3 S3 mem md regs true idv F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 (gp0_in_byte_rng cx (lm_k m + 1)) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra idv))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra idv)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (E32 : ew E 32 = Z_to_bv 64 idv)
      by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok RUN HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: not taken, t1 = in.n - k - 1 > 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_eq in Hc. lia.
    + (* 0x849a8-0x849d0: the trap (not taken), the instrumented check of in.p[0], the cursor, s5 = in.p[0] *)
      paj_run_to_tok RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with (tv + 1)
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 1) (tv + 1) RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with (c_n cx - lm_k m - 1 + -1)
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SOff 6 (-1)) (c_n cx - lm_k m - 1 + -1) RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E6, unsigned_lit_small by lia. reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra idv)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = in.p[0] (atom 32) *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite ?E32, ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
      unfold gn_id, gn_more. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [_ | Hlt]; [reflexivity | lia].
  - (* in.n = 0 after the op byte: fuzz_u8 gives 0 and consumes nothing *)
    assert (P6 : false = true -> val_mem segs (arm W mem) tv 1 0 /\
       exists p n, In (p, n) (ablocks B ly3 S3) /\ p <= tv /\ tv + 1 <= p + req_size n) by discriminate.
    destruct (gp0_entry W ly3 S3 mem md regs false 0 F tv HAR R9 R20' R23 R27
      P1 P2 HF32 P3 P4 P5 ltac:(lia) P6) as [HS SHOK].
    set (E := Eimg (Ereg regs (gp0_extra 0))) in *.
    assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
    assert (HAE : env_agree 32 (Ereg regs (gp0_extra 0)) E)
      by (subst E; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
    assert (EEo : forall q (rr : bv 5), Z.of_nat q = bv_unsigned rr -> ew E q = getr regs rr)
      by (intros q rr Hq; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
          rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hq).
    assert (E9 : ew E 9 = Z_to_bv 64 F) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
    assert (E20 : ew E 20 = Z_to_bv 64 tv) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20').
    assert (E6 : ew E 6 = Z_to_bv 64 (c_n cx - lm_k m - 1)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6').
    assert (E25 : ew E 25 = Z_to_bv 64 t) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25').
    assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; lia).
    clearbody E.
    unfold cfg_at. change (w64 (fr_B0 + fr_arm 5)) with (Z_to_bv 64 (BASE + AF_arm_gone)).
    (* 0x849a0 sd s9,88(s1) *)
    paj_run_tok RUN HS HJ SHOK gp0_Bspan.
    { gp0_awr U9. }
    (* 0x849a4 beqz t1: taken, t1 = 0 *)
    psrr_branch_tok RUN BR HS SHOK gp0_Bspan.
    + (* 0x84a9c-0x84aa4: F+144 = 0, s5 = 0, F+16 = in.p *)
      paj_run_to_tok RUNTO HS HJ SHOK gp0_Bspan AF_gn_join.
      { gp0_awr U9. }
      lazymatch goal with Hg : mem_grows _ _ |- _ => rename Hg into HGr end.
      assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
      { intros a Ha Hna Hnt Hnb.
        rewrite (aview_kept_out _ _ _ _ _ HFr0 a Ha); [| gp0_nowr U9 Hna Hnt Hnb].
        apply (aview_kept_out _ _ _ _ _ HFr a Ha). gp0_nowr U9 Hna Hnt Hnb. }
      assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms0)) a).
      { intros a Hw. apply (writable_kept (w_H W) (ms_mem ms) (ms_mem ms0) a);
          [intros Hp; exact (gp0_pres_grows W _ _ a HGr Hp)|].
        apply (writable_kept (w_H W) mem (ms_mem ms) a); [intros Hp; exact (gp0_pres_grows W _ _ a HG0 Hp) | exact Hw]. }
      assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 16 <= a < F + 24) -> ~ (F + 88 <= a < F + 96) ->
          ~ (F + 144 <= a < F + 152) -> abyte_kept W mem W (ms_mem ms0) a)
        by (intros a Ha Hna Hnt Hnb; split; [exact (K1 a Ha Hna Hnt Hnb) | apply WK]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG0. cbn [ms_mem restrict] in RG0.
      pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
      pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
      assert (SV88 : sv8 W (ms_mem ms0) (F + 88) t).
      { unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 88 8%N (SOff 25 0) t RG1) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV16 : sv8 W (ms_mem ms0) (F + 16) (c_p cx + gn_kq cx m)).
      { replace (c_p cx + gn_kq cx m) with tv
          by (unfold gn_kq, gn_more, tv; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 16 8%N (SOff 20 0) tv RG0) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        - zside.
        - zside. }
      assert (SV144 : sv8 W (ms_mem ms0) (F + 144) (c_n cx - gn_kq cx m)).
      { replace (c_n cx - gn_kq cx m) with 0
          by (unfold gn_kq, gn_more; destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia).
        unfold sv8.
        lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
          apply (field_of_region Ev _ 9%nat F _ _ _ _ _ 144 8%N (SLit 0) 0 RG2) end.
        - rewrite ?ew_ewset_other by lia. exact U9.
        - left. reflexivity.
        - reflexivity.
        - zside.
        - zside. }
      lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        assert (HAE2 : env_agree 32 (Ereg regs (gp0_extra 0)) Ev)
          by (split; [intros q Hq; rewrite ?ew_ewset_other by lia; exact (proj1 HAE q Hq)
                     | rewrite ?ed_ewset; exact (proj2 HAE)]) end.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ GP0_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (KK : forall rr, In rr GP0_KEPT -> getr (ms_regs ms0) rr = getr regsD rr).
      { intros rr Hrr. rewrite (KR rr Hrr). apply KR0. cbv [GP0_KEPT In] in Hrr.
        repeat (destruct Hrr as [<- | Hrr]; [cbv; tauto|]). destruct Hrr. }
      destruct (gp0_kregs cx FF regsD (ms_regs ms0) KK HCOM) as (KRG & Q24 & Q26).
      (* s5 = 0 *)
      prreg HS (21%bv : bv 5) Q21.
      pmkst HS. apply SRr_ret. exists m.
      apply (gp0_close cx t m W mem (ms_mem ms0) md _ (ms_regs ms0) ly3 S3 k fpos HB HAR HJ HFR HFL HMOD HIN HRV HROM
               HSEP HLS HRI HOP KEEP WK SV16 SV144 SV88 KRG Q24 Q26).
      rewrite Q21. unfold gn_id, gn_more.
      destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)) as [Hlt | _]; [lia | reflexivity].
    + (* 0x849a4 beqz t1 not taken: t1 = in.n - k - 1 = 0, no such state *)
      exfalso. rewrite branch_eq_U, (U_atom E 6 _ E6), U_lit in Hc by lia. apply Z.eqb_neq in Hc. lia.
Qed.

End gp0.
