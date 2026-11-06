(* LLVMFuzzerTestOneInput_segX_up_b: the second stretch of the image-B `up` segment of LLVMFuzzerTestOneInput,
   +0x8a4 .. +0x8dc: the upstream buffer's size (`blt zero, s5` at +0x8a4 and its two arms, +0x8a8 / +0x8b0..+0x8bc),
   malloc #3 (+0x8c4, YC85.v amalloc04_sub), its NULL check (+0x8c8, the abort edge into +0xb88 refuted by
   4096 <= the block), and __asan_memset of the buffer with the fill 0xa5 (+0x8d8, YC85.v aj_intrin_atS).
   Ports cgif lib/A/ACf2.v's malloc stage (the call-rule application and the post's block / meter bookkeeping)
   and lib/A/ACf0.v's memset stage. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal YC85 DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBList DecodeBAddr DecodeBPa DecodeBImg DecodeBPaLib.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_segX_up_arith LLVMFuzzerTestOneInput_segX_up_den LLVMFuzzerTestOneInput_segX_up_a
LLVMFuzzerTestOneInput_segX_exit_defs LLVMFuzzerTestOneInput_segX_up_kit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN1y.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* YM03.v:182-189 redefines lia / nia globally (context pruning and retries); this file uses the originals
   (YM03.v:179-180). *)
Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Local Ltac Lia.nia ::= Zify.zify; xnia zchecker.

(* Read register r off a symbolic state, whose value there is e, and rewrite the goal's getr with it. *)
Ltac up_rege HS r e :=
  lazymatch type of HS with
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    let Hr := fresh "Hr" in pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
    change (sr_get (ss_regs ss) r) with e in Hr; rewrite Hr; clear Hr
  | st_ok_pi ?sg ?val ?E ?ss (restrict ?H ?ms) =>
    let Hr := fresh "Hr" in pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    change (sr_get (ss_regs ss) r) with e in Hr; rewrite Hr; clear Hr
  end.

(* The registers a run kept, at the run's stop. *)
Ltac up_kept HS regs extra keep HAE :=
  lazymatch type of HS with
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    intros x Hx; exact (regs_kept_of_st_ok sg E ss (restrict H ms) regs extra keep HS HAE
                          ltac:(vm_compute; reflexivity) x Hx)
  | st_ok_pi ?sg ?val ?E ?ss (restrict ?H ?ms) =>
    intros x Hx; exact (regs_kept_of_st_ok_pi E ss (restrict H ms) regs extra keep HS HAE
                          ltac:(vm_compute; reflexivity) x Hx)
  end.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation SEGS := (@pa_segs _ decodeb_listing PI_decodeb).
#[local] Abbreviation VAL := (@pa_val _ decodeb_listing PI_decodeb).
#[local] Abbreviation BASE := (@pa_val _ decodeb_listing PI_decodeb A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variable RA : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HPCM : pc_wrap_malloc (as_code B) = decodeb_sigma DB___interceptor_trampoline_malloc.
Hypothesis HUTR : dec_llvmf_utraces RA B.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis HROS : dec_ro_rd_unowned B.
Hypothesis HRNE : dec_rom_no_errno B.
Hypothesis AMALLOC : @amalloc04_rule fx rc dec_B_sink_head SEGS B MT.
Hypothesis AMEMSET : @aintrin_realizes fx rc SEGS B OSet (decodeb_sigma DB___asan_memset).
Let RUN := @paj_run fx rc dec_B_sink_head decodeb_listing PL_decodeb PI_decodeb B LAWS.
Let BR := @paj_branch fx rc decodeb_listing PI_decodeb.

Definition up_len (cx : dctx) : Z := dec_b_len (d_n cx).
Definition up_r (cx : dctx) : Z := upstream_result (up_len cx).
Definition up_uo (cx : dctx) : Z := dec_b_uolen (up_r cx).

Lemma up_cfg_eq : forall regs mem md X,
  mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + X)) mem (YK11.seg_rom decodesegsB0)) md =
  mkCfg (mkst regs (Z_to_bv 64 (BASE + X)) mem (seg_rom SEGS)) md.
Proof. intros. reflexivity. Qed.

(* A symbolic state with no tracked memory, at any pc of the listing. *)
Lemma up_seat0 : forall pc regs (W : world SEGS) mem,
  st_ok_pi SEGS VAL (EUP regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS UPBx [] (EUP regs) (mrestrict (w_H W) mem).
Proof.
intros pc regs W mem. rewrite restrict_mkst_fx. split; [|apply Forall_nil].
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | reflexivity | apply Forall_nil | exact I |].
split; [exact I | split; exact I].
Qed.

Lemma up_uo_bounds : forall cx, 0 <= d_n cx < 67108864 -> 1 <= up_uo cx <= 1440.
Proof.
intros cx Hn. pose proof (up_olen_bounds (up_len cx) ltac:(unfold up_len, dec_b_len, UP_NMAX; lia)) as H.
unfold up_uo, up_r, dec_b_uolen. unfold up_olen in H. exact H.
Qed.

(* The registers of the entry configuration are the env's atoms below 32 (EUP_reg of segX_up_a, here for the
   seat's env), and the seat env agrees with the entry registers below 32. *)
Lemma up_agree : forall regs, env_agree 32 (Ereg regs up_extra) (EUP regs).
Proof.
intros regs. split; [intros n Hn; unfold EUP; first [apply Eimg_low | symmetry; apply Eimg_low]; unfold A_TEXT; lia
  | reflexivity].
Qed.

(* The registers +0x8a4 .. +0x8c4 leave alone. *)
Definition up_keepB1 : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 25%bv; 26%bv; 27%bv].

(* A symbolic value whose unsigned reading is z is the word z. *)
Lemma up_w64_of_U : forall E v z, U E v = z -> 0 <= z < 18446744073709551616 -> sv_denot E v = w64 z.
Proof.
intros E v z H Hz. apply bv_eq. unfold U in H. rewrite H. unfold w64. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with 18446744073709551616. symmetry. apply Z.mod_small. exact Hz.
Qed.

(* +0x8a4 .. +0x8c4: the upstream buffer's size (`blt zero, s5` and its two arms) into a0 and s8, then the jump
   into malloc. *)
Lemma up_B1 : forall (W : world SEGS) regs mem md r (Q : world SEGS -> config -> Prop)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc k,
  @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  getr regs 21 = w64 r -> -1 <= r <= 40 ->
  (forall regsT mdT,
     getr regsT 10 = w64 (dec_b_uolen r) -> getr regsT 24 = w64 (dec_b_uolen r) ->
     getr regsT 1 = Z_to_bv 64 (BASE + 0x8c8) ->
     (forall x, In x up_keepB1 -> getr regsT x = getr regs x) ->
     @ajournal rc dec_B_sink_head SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem mdT k ->
     SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (decodeb_sigma DB___interceptor_trampoline_malloc)) mem
       (seg_rom SEGS)) mdT) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x8a4)) mem (seg_rom SEGS)) md) Q.
Proof.
intros W regs mem md r Q STK sp0 FP ly S W0 mem0 md0 own lyc Sc k HJ H21 Hr HK.
destruct (up_seat0 0x8a4 regs W mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (EUP regs)) by (unfold EUP; apply Eimg_env).
assert (E21 : ew (EUP regs) 21 = Z_to_bv 64 r) by (rewrite (EUP_reg regs 21%bv 21 eq_refl); exact H21).
psrr_branch_tok RUN BR HS SHOK UPspan; rename Hc into Hb;
  rewrite (up_lt0_s5 (EUP regs) r E21 Hr) in Hb.
- apply Z.ltb_lt in Hb.
  assert (Huo : dec_b_uolen r = 36 * r) by (unfold dec_b_uolen; replace (0 <? r) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
  paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|].
  up_memeq HF. pmkst HS. cbn [pa_sigma PI_decodeb] in *.
  rewrite Hmem. rewrite Hmem in HJ. apply HK.
  + up_rege HS (10%bv : bv 5) up_sa0b. rewrite Huo.
    apply up_w64_of_U; [exact (up_U_sa0b (EUP regs) r E21 ltac:(lia)) | lia].
  + up_rege HS (24%bv : bv 5) up_s8. rewrite Huo.
    apply up_w64_of_U; [exact (up_U_s8 (EUP regs) r E21 ltac:(lia)) | lia].
  + up_rege HS (1%bv : bv 5) (SOff 240 2248). exact (codeptr_val (EUP regs) 2248 HEI).
  + up_kept HS regs up_extra up_keepB1 (up_agree regs).
  + exact HJ.
- apply Z.ltb_ge in Hb.
  assert (Huo : dec_b_uolen r = 1) by (unfold dec_b_uolen; replace (0 <? r) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
  paj_run_tok RUN HS HJ SHOK UPspan; [apply awr_ok_nil|].
  up_memeq HF. pmkst HS. cbn [pa_sigma PI_decodeb] in *.
  rewrite Hmem. rewrite Hmem in HJ. apply HK.
  + up_rege HS (10%bv : bv 5) (SLit 1). rewrite Huo. reflexivity.
  + up_rege HS (24%bv : bv 5) (SLit 1). rewrite Huo. reflexivity.
  + up_rege HS (1%bv : bv 5) (SOff 240 2248). exact (codeptr_val (EUP regs) 2248 HEI).
  + up_kept HS regs up_extra up_keepB1 (up_agree regs).
  + exact HJ.
Qed.

(* A block appended to the live blocks is disjoint from every block before it. *)
Lemma up_new_disj : forall ly S W mem md bl p n b m,
  AR SEGS B ly S W mem md -> ablocks B ly S = bl ++ [(b, m)] -> In (p, n) bl ->
  forall i j, 0 <= i < req_size n -> 0 <= j < req_size m -> p + i <> b + j.
Proof.
intros ly S W mem md bl p n b m HAR Hbl Hin i j Hi Hj.
apply in_split in Hin as (l1 & l2 & ->).
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md (p, n) (b, m) l1 l2 [] HAR) as Hd.
rewrite Hbl, <- app_assoc in Hd. cbn [app] in Hd. specialize (Hd eq_refl).
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* malloc #3 at +0x8c4 (YC85.v amalloc04_sub, cgif lib/A/ACf2.v:116-137): from the call's entry configuration to
   +0x8c8 with the new block in a0, the meter charged, and every clause the segment carries kept (the mode's table
   words through the read-only view at both states, from the entry's rom_view and the two journals). *)
Lemma up_malloc_call : forall cx ly' S' (W : world SEGS) regsT memT md' res mode nch ns
    (Q : world SEGS -> config -> Prop),
  up_base RA cx -> rom_view SEGS (d_W cx) (d_mem cx) ->
  dec_b_core B cx ly' S' W regsT memT md' dec_ev_840 ->
  Permutation (ablocks B ly' S') (ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)]) ->
  4096 <= res ->
  mo_le MT (d_S cx) S' (dec_spent_840 MT (d_n cx)) -> mo_ok MT S' (dec_rest_840 MT) ->
  up_mem cx W memT res mode nch ns ->
  getr regsT 10 = w64 (up_uo cx) -> getr regsT 1 = Z_to_bv 64 (BASE + 0x8c8) ->
  getr regsT 18 = w64 SHADOW_OFF -> getr regsT 21 = w64 (up_r cx) -> getr regsT 22 = w64 (up_len cx) ->
  getr regsT 24 = w64 (up_uo cx) -> getr regsT 27 = w64 res ->
  (forall W2 regs2 mem2 md2 ly2 S2 upb,
     dec_b_core B cx ly2 S2 W2 regs2 mem2 md2 dec_ev_96c ->
     Permutation (ablocks B ly2 S2) (ablocks B (d_ly cx) (d_S cx) ++ [(res, up_len cx)] ++ [(upb, up_uo cx)]) ->
     ablocks B ly2 S2 = ablocks B ly' S' ++ [(upb, up_uo cx)] ->
     4096 <= upb ->
     mo_le MT (d_S cx) S2 (dec_spent_96c MT (d_n cx)) -> mo_ok MT S2 (dec_rest_96c MT) ->
     up_mem cx W2 mem2 res mode nch ns ->
     getr regs2 10 = w64 upb -> getr regs2 18 = w64 SHADOW_OFF -> getr regs2 21 = w64 (up_r cx) ->
     getr regs2 22 = w64 (up_len cx) -> getr regs2 24 = w64 (up_uo cx) -> getr regs2 27 = w64 res ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x8c8)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_malloc (as_code B))) memT (seg_rom SEGS)) md') Q.
Proof.
intros cx ly' S' W regsT memT md' res mode nch ns Q HB HROM Hcore Hperm Hres Hmle Hmok Hmem Ha0 Hra H18 H21 H22 H24 H27
  HK.
pose proof HB as (Hch & Hstk & Hra4 & HRA & Hnev0 & Hlive0 & Hn & Hnlen).
pose proof Hcore as (HJ & Hfrs & Hs0 & Hs1 & Hsp & Hsp1r & Hsp1al & Hgp & Htp & Hsaved & HF4096 & HFal & HFpres &
  HFLw & Hpay & Hgarr).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & Hk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : DEC_LLVMF_STK = 32768) by reflexivity.
assert (HAS : ASTACK = 16384) by reflexivity.
pose proof (up_uo_bounds cx Hn) as Huo.
assert (HLEN : 0 <= up_len cx <= 67108864) by (unfold up_len, dec_b_len; lia).
up_lits.
assert (Hs0Z : s0Z regsT = d_sp0 cx) by (unfold s0Z; rewrite Hs0; apply unsigned_lit_small; lia).
assert (HBASE : BASE = 0x800b0) by reflexivity.
assert (HraZ : raZ regsT = DEC_A_LLVMF + 0x8c8) by (unfold raZ; rewrite Hra, HBASE; reflexivity).
assert (Hraz4 : 4096 <= raZ regsT) by (rewrite HraZ; unfold DEC_A_LLVMF; vm_compute; discriminate).
assert (Ho16 : (d_sp1 cx - d_sp0 cx) mod 16 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp1al; [|lia]. apply Z.mod_divide in Hsp0al; [|lia].
  destruct Hsp1al as [q1 Hq1]. destruct Hsp0al as [q0 Hq0]. exists (2 * q1 - q0). lia. }
assert (Hlive : blocks_bytes S' + up_uo cx <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ Hperm), bsum_app, <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)).
  cbn [bsum fold_right snd]. unfold DEC_LIVE_LIB in Hlive0. up_lits. lia. }
eapply SRr_bind.
{ eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT AMALLOC W regsT memT DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md' dec_ev_840
    (up_uo cx) (d_sp1 cx - d_sp0 cx) (Z_to_bv 64 (BASE + 0x8c8)) (ex_ch cx) HJ).
  - exact Ha0.
  - unfold MALLOC_MAX. lia.
  - exact Hlive.
  - rewrite Hsp. lia.
  - exact Ho16.
  - lia.
  - rewrite HAS, FFS. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - apply ret_ok_codeptr_v; [change (2 ^ 40) with 1099511627776; lia | reflexivity].
  - unfold dec_ev_840 in Hnev. unfold DEC_EV_LIB in Hnev0. lia.
  - exact (up_chain_pre B RA cx ly' S' W regsT memT md' dec_ev_840 regsT HB Hcore Hsp Hs0Z Hraz4).
  - apply (up_trace_in RA cx regsT (pc_malloc_ra0 (as_code B)) (as_universe B) (DEC_A_LLVMF + 0x8c8) HB HraZ).
    intros sp Hsp'. apply (proj1 (HUTR sp Hsp')). unfold DEC_LLVMF_RA_MALLOC. cbn [map In].
    right; right; left; reflexivity.
  - apply (mo_ok_le MT MTL S' (mo_malloc MT (up_uo cx)) (dec_rest_840 MT) Hmok).
    unfold dec_rest_840, dec_rest_96c, dec_crt_cost_max.
    pose proof (mo_malloc_mono MT MTL (up_uo cx) 1440 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & upb & -> & HJ2 & HP & Hres2 & Hfr2 & Hupb & Hbl & HKc & MLE & _).
pose proof (proj1 HJ2) as HAR2.
assert (Hin_pl : 0 < d_n cx -> In (d_p cx, d_n cx) (ablocks B ly' S')) by exact Hpay.
assert (Hin_res : In (res, up_len cx) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_app_iff; right; left; reflexivity).
assert (Hnew2 : In (upb, up_uo cx) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_app_iff; right; left; reflexivity).
assert (Hfin2 : In (DEC_FCLASS, d_fpos cx) (frames S2)) by (rewrite Hfr2, Hfrs; left; reflexivity).
pose proof (proj1 (proj2 HJ2)) as Hly2.
assert (EFA2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx).
{ pose proof Hly2 as (_ & _ & _ & _ & _ & HlyF & _). unfold d_F, frame_addr. rewrite HlyF. reflexivity. }
assert (HnZ : forall a, d_F cx <= a < d_F cx + 64 \/ d_SH cx <= a < d_SH cx + 8 -> ~ (upb <= a < upb + req_size (up_uo cx))).
{ intros a Ha Hb. apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 mem2 md2 upb (up_uo cx) (a - upb) DEC_FCLASS (d_fpos cx)
    HAR2 Hnew2 Hfin2 ltac:(lia)).
  replace (upb + (a - upb)) with a by ring. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA2.
  change (fs_frame_bytes DEC_FCLASS) with 64. change (64 / 8) with 8. unfold d_SH in Ha. lia. }
destruct (ex_acall_keep B LAWS cx ly' S' W regsT memT md' dec_ev_840 W2 mem2
  (d_sp0 cx + (d_sp1 cx - d_sp0 cx) - ASTACK) (d_sp0 cx + (d_sp1 cx - d_sp0 cx))
  (fun a => upb <= a < upb + req_size (up_uo cx)) Hcore HKc ltac:(lia)
  ltac:(intros a Ha; apply HnZ; left; exact Ha) ltac:(intros a Ha; apply HnZ; right; exact Ha)) as (KS & KF & KH).
pose proof HKc as (_ & KB & _).
assert (KR : forall p n, In (p, n) (ablocks B ly' S') -> forall i, 0 <= i < req_size n ->
  aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W) memT (p + i)).
{ intros p n Hpn i Hi. apply (KB p n i Hpn Hi). intros Hb.
  apply (up_new_disj ly2 S2 W2 mem2 md2 (ablocks B ly' S') p n upb (up_uo cx) HAR2 Hbl Hpn i (p + i - upb) Hi);
    [lia | ring]. }
assert (KP : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regsT (Z_to_bv 5 r)) by exact HP.
assert (MLE2 : mo_le MT (d_S cx) S2 (dec_spent_96c MT (d_n cx))).
{ apply (mle_weaken MT (d_S cx) S2 (dec_spent_840 MT (d_n cx) + mo_malloc MT (up_uo cx))); [exact MTL | |].
  - exact (mle_station MT (d_S cx) S' S2 _ _ MTL Hmle MLE).
  - unfold dec_spent_96c. pose proof (mo_malloc_mono MT MTL (up_uo cx) 1440 ltac:(lia)). lia. }
assert (MOK2 : mo_ok MT S2 (dec_rest_96c MT)).
{ apply (mok_station MT S' S2 (dec_rest_840 MT) (mo_malloc MT (up_uo cx)) (dec_rest_96c MT) MTL Hmok MLE).
  - unfold dec_rest_96c, dec_crt_cost_max.
    pose proof (mo_malloc_nonneg MT MTL 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT MTL 1016 ltac:(lia)).
    pose proof (mo_malloc_nonneg MT MTL 1440 ltac:(lia)). pose proof (mo_free_nonneg MT MTL). lia.
  - unfold dec_rest_840. pose proof (mo_malloc_mono MT MTL (up_uo cx) 1440 ltac:(lia)). lia. }
apply (HK W2 regs2 mem2 md2 ly2 S2 upb).
- change dec_ev_96c with (dec_ev_840 + 1).
  apply (ex_core_kept B cx ly' S' W regsT memT md' dec_ev_840 ly2 S2 W2 regs2 mem2 md2 (dec_ev_840 + 1) Hcore HJ2).
  + rewrite Hfr2. exact Hfrs.
  + exact (KP 8 ltac:(unfold acallee_saved; lia)).
  + exact (KP 9 ltac:(unfold acallee_saved; lia)).
  + unfold spZ. exact (f_equal bv_unsigned (KP 2 ltac:(unfold acallee_saved; lia))).
  + exact (KP 3 ltac:(unfold acallee_saved; lia)).
  + exact (KP 4 ltac:(unfold acallee_saved; lia)).
  + intros a Ha. apply KS. lia.
  + intros a Ha. exact (proj1 (KF a Ha)).
  + intros a Ha. exact (proj2 (KF a Ha)).
  + intros Hn0. rewrite Hbl. apply in_app_iff. left. exact (Hin_pl Hn0).
  + intros i Hi. destruct (Z.lt_ge_cases 0 (d_n cx)) as [Hn0 | Hn0]; [|lia].
    apply (KR (d_p cx) (d_n cx) (Hin_pl Hn0) i). pose proof (req_size_pos (d_n cx) ltac:(lia)). lia.
- rewrite Hbl. rewrite app_assoc. apply Permutation_app_tail. exact Hperm.
- exact Hbl.
- exact Hupb.
- exact MLE2.
- exact MOK2.
- apply (up_mem_kept B cx ly' S' W memT md' ly2 S2 W2 mem2 md2 res mode nch ns HCELLS HAR HAR2
    (up_rom_rd B cx ly' S' W regsT memT md' dec_ev_840 HROS HRNE HROM Hcore)
    (ex_rom_rd B cx _ _ _ _ _ _ _ _ HROS HRNE HROM HJ2) Hsp1r).
  + intros a Ha. apply KS. lia.
  + intros a Ha. exact (proj1 (KF a Ha)).
  + intros a Ha. exact (KH a Ha).
  + intros i Hi. apply (KR res (up_len cx) Hin_res i).
    pose proof (req_size_pos (up_len cx) ltac:(lia)).
    assert (Hlb : Z.of_nat (length (d_body cx)) = up_len cx).
    { unfold d_body, up_len, dec_b_len, dec_b_u. rewrite length_skipn. lia. }
    lia.
  + exact Hmem.
- exact Hres2.
- transitivity (getr regsT 18); [exact (KP 18 ltac:(unfold acallee_saved; lia)) | exact H18].
- transitivity (getr regsT 21); [exact (KP 21 ltac:(unfold acallee_saved; lia)) | exact H21].
- transitivity (getr regsT 22); [exact (KP 22 ltac:(unfold acallee_saved; lia)) | exact H22].
- transitivity (getr regsT 24); [exact (KP 24 ltac:(unfold acallee_saved; lia)) | exact H24].
- transitivity (getr regsT 27); [exact (KP 27 ltac:(unfold acallee_saved; lia)) | exact H27].
Qed.

End g.
