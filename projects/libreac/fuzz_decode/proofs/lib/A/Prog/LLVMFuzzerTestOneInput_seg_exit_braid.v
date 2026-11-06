(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 257 of its 330 lines of code are new or changed and 508 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_exit_braid: the check_braid piece of the exit segment of the image-A walk of
   libreac/fuzz_decode's LLVMFuzzerTestOneInput (ex_braid_stmt of lib/A/Prog/LLVMFuzzerTestOneInput_seg_exit_cuts.v).

   ex_braid_ok : ex_braid_stmt. From ex_st_978 to ex_st_98c: +0x978 .. +0x984 (DecodeList.v:634-637: li a3,12;
   mv a0,s2 (s2 = res + 50); mv a1,s7 (upb); mv a2,s6 (nch)), stepped by the Pa engine, and the `jal check_braid` at
   +0x988 (DecodeList.v:638, PCall DS_check_braid, return +0x98c), discharged by the leaf contract check_braid_cg.v's
   dec_check_braid_cg at check_braid_c.CHECK_BRAID = decode_sigma DS_check_braid. The call is composed into the walk's
   journal by ex_braid_call below through the shared bridge LLVMFuzzerTestOneInput_leafb.v (dec_leafb_journal: YC85.v
   aj_intrin_atS's form, the leaf's dleaf_post turned into the caller's journal by YCbq.v ajournal_after_write).
   The leaf adds no model event: the journal at +0x98c keeps k = dec_ev_86c + DEC_CRT_EV, and the memory changes only
   in the leaf's stack window below sp.

   The C facts and memory helpers are the crt piece's (LLVMFuzzerTestOneInput_seg_exit_crt.v: ex_up_geom, ex_crt_braid,
   ex_garr8_kept, ex_rdword_kept, ex_saved_at_range, ex_body_len, reg_at, awr_ro_rec), and the proof steps follow its
   ex_crt_ok; this file holds only what is check_braid's own: the leaf's entry address, braid_map from the view, the
   call, and the cut ex_st_98c. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YG0s YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
  DecodeSyms DecodeList DecodeAddr DecodePa DecodePaLib DecodeImg YC4b YC1g YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_seg_exit_cuts LLVMFuzzerTestOneInput_leafb
  LLVMFuzzerTestOneInput_seg_exit_crt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require check_braid_cg check_braid_c AsanKA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module ACellsB := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
Module AKAB := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.AsanKA.
Module CBc := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_c.
Module LBraidCg := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_braid_cg.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it (ReadName.v's line). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 1. The call of check_braid, composed into the caller's journal        *)
(* ------------------------------------------------------------------ *)

(* The leaf's entry is the listing's: decode_sigma DS_check_braid is check_braid_c.v's CHECK_BRAID (both computed). *)
Lemma ex_braid_sigma : decode_sigma DS_check_braid = CBc.CHECK_BRAID.
Proof. vm_compute. reflexivity. Qed.

Section call. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := decodesegs0.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HCELLS : dec_crt_cells B.

(* check_braid_c.v's braid_map (raw reads Mem.mrd) from the same relation read through the view. *)
Lemma ex_braid_map : forall (W : world segs) mem audio pcm nch ns,
  dec_crt_braid (aview segs (w_H W) mem) audio pcm nch ns -> CBc.braid_map mem audio pcm nch ns.
Proof.
intros W mem audio pcm nch ns H ch s j Hch Hs Hj.
destruct (H ch s j Hch Hs Hj) as (v & H1 & H2).
destruct (dec_leafb_mrd_aview W mem _ v H1) as (b1 & E1 & V1).
destruct (dec_leafb_mrd_aview W mem _ v H2) as (b2 & E2 & V2).
exists b1. split; [exact E1|]. transitivity (Some b2); [exact E2|]. f_equal. apply bv_eq. lia.
Qed.

(* The call lemma: check_braid (audio, pcm, nch, ns) at a generic float state and registers, from the caller's journal
   at the call memory; the leaf adds no event, so the journal at the return keeps k. Premises in YC85.v
   aj_intrin_atS's form (the leaf's stack window inside the journal's, gp / tp / ra), the two buffers inside caller
   blocks, and the braid relation through the view. *)
Lemma ex_braid_call : forall (fx : YK11.FPState),
  @dec_leaf_at rc B (@LBraidCg.dec_check_braid_cg) fx ->
  forall (W : world segs) (regsT : bvmap 5 word) memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z)
         (audio pcm nch ns bA nA bP nP : Z),
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 audio -> getr regsT 11 = w64 pcm -> getr regsT 12 = w64 nch -> getr regsT 13 = w64 ns ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  YK0s.ret_ok (getr regsT 1) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  1 <= nch <= 127 -> 1 <= ns <= 127 ->
  In (bA, nA) (ablocks B lyc Sc) -> bA <= audio -> audio + 3 * nch * ns + 3 * (nch mod 2) <= bA + nA ->
  In (bP, nP) (ablocks B lyc Sc) -> bP <= pcm -> pcm + 3 * nch * ns <= bP + nP ->
  dec_crt_braid (aview segs (w_H W) memT) audio pcm nch ns ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (decode_sigma DS_check_braid)) memT (YK11.seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 (getr regsT 1) mem2 (YK11.seg_rom segs)) md2 /\
       @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros fx LEAF W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o audio pcm nch ns bA nA bP nP
  HJ Ha0 Ha1 Ha2 Ha3 Hsp Hal Hneg Hbud Hra Hgp Htp Hnch Hns HinA HA1 HA2 HinP HP1 HP2 HBR.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Cc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bA nA HAR HinA) as (_ & A4096 & Aceil & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bP nP HAR HinP) as (_ & P4096 & Pceil & _).
assert (RA : nA <= req_size nA) by (clear; unfold req_size; destruct (Z.eqb_spec nA 0); lia).
assert (RP : nP <= req_size nP) by (clear; unfold req_size; destruct (Z.eqb_spec nP 0); lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hspz : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = spZ regsT) by reflexivity.
(* the arithmetic, each fact in a small context *)
assert (Hspr : alloc_ceiling + 4096 <= spZ regsT <= 2 ^ 47 /\ sp0 - STK <= spZ regsT - 4096 /\ spZ regsT <= sp0)
  by (clear - Hsp Hneg Hbud Hes Hceil Hslo Hshi H47; rewrite Hes in Hbud; lia).
assert (HL : 3 <= 3 * nch * ns) by (clear - Hnch Hns; nia).
assert (Hm2 : 0 <= nch mod 2 < 2) by (clear - Hnch; apply Z.mod_pos_bound; lia).
assert (HAb : 4096 <= audio /\ audio + 3 * nch * ns + 3 * (nch mod 2) <= bA + req_size nA /\
  bA + req_size nA <= alloc_ceiling) by (clear - A4096 Aceil HA1 HA2 RA; lia).
assert (HPb : 4096 <= pcm /\ pcm + 3 * nch * ns <= bP + req_size nP /\ bP + req_size nP <= alloc_ceiling)
  by (clear - P4096 Pceil HP1 HP2 RP; lia).
rewrite ex_braid_sigma.
eapply SRr_mono.
{ apply (dec_leafb_journal (fx := fx) (SK := dec_A_sink_head) B LAWS W regsT memT STK sp0 FP ly S W0 mem md own lyc
    Sc mdc k o CBc.CHECK_BRAID None [] (fun _ => True) HJ Hsp Hal Hneg Hbud Hra Hgp Htp).
  - intros a Ha. inversion Ha.
  - intros HPRE.
    refine (LEAF lyc Sc W regsT memT mdc audio pcm nch ns (spZ regsT - 4096) HPRE Ha0 Ha1 Ha2 Ha3 Hnch Hns
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    unfold CBc.CHECK_BRAID_FRAME.
    + clear - HAb Cc HL Hm2; lia.
    + clear - HPb Cc HL; lia.
    + exact (ex_braid_map W memT audio pcm nch ns HBR).
    + eapply (dec_leafb_stk_journal (SK := dec_A_sink_head)); [exact HJ | clear - Hspr; lia | clear - Hspr Hspz; lia].
    + clear - Hspz; lia.
    + left. clear - HAb Hspr Hspz; lia.
    + left. clear - HPb Hspr Hspz; lia.
    + exact (dec_leafb_asan_cells B HCELLS lyc Sc W memT mdc HAR).
    + apply dec_leafb_app_stack. clear - Hspr Hspz; lia.
    + apply dec_leafb_app_stack. clear - Hspr Hspz Cc; lia.
    + unfold AKAB.off_stk, ACellsB.MIDEND, ACellsB.GOT_CELL_K. left. clear - Hspr Hspz Cc; lia.
    + apply (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc bA nA);
        [exact HAR | exact HinA | exact HA1 | clear - HL Hm2; lia | clear - HAb; lia].
    + apply (dec_leafb_addressable_block B LAWS lyc Sc W memT mdc bP nP);
        [exact HAR | exact HinP | exact HP1 | clear - HL; lia | clear - HPb; lia].
    + eapply (dec_leafb_rng_journal (SK := dec_A_sink_head));
        [exact HJ | clear - Hspr Hspz; lia | clear - Hspr Hspz; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + apply (dec_leafb_rng_block B LAWS lyc Sc W memT mdc bP nP); [exact HAR | exact HinP | exact HP1 | clear - HPb; lia].
    + apply (dec_leafb_rng_block B LAWS lyc Sc W memT mdc bA nA); [exact HAR | exact HinA | exact HA1 | clear - HAb; lia].
    + apply (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bP nP);
        [exact HAR | exact HinP | exact HP1 | clear - HL; lia | clear - HPb; lia].
    + apply (dec_leafb_rng_shadow_block B LAWS lyc Sc W memT mdc bA nA);
        [exact HAR | exact HinA | exact HA1 | clear - HL Hm2; lia | clear - HAb; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hfr & Hgr & _).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [intros a Ha Hw; apply (Hfr a Ha Hw); intros H; inversion H | exact Hgr].
Qed.
End call.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic state at +0x978                                      *)
(* ------------------------------------------------------------------ *)

(* The four moves and the jal read no memory: no region, no fact. Atom 32 is the token engine's Bx (the shadow base),
   which no instruction here uses. *)
Definition ex_br_ss : sstate := mkSS 0x978 sr_atoms [] None (mkFacts [] [] []).

Section en. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation SEGS := (@pa_segs _ decode_listing PI_decode).
Local Abbreviation VAL := (@pa_val _ decode_listing PI_decode).
Local Abbreviation BASE := (@pa_val _ decode_listing PI_decode A_TEXT).
Definition EBR (regs : bvmap 5 word) : env := Eimg (PI := PI_decode) (Ereg regs [Z_to_bv 64 SHADOW_OFF]).
Lemma ex_br_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (EBR regs) ex_br_ss
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + 0x978)) mem (YK11.seg_rom SEGS))).
Proof.
intros W regs mem. rewrite restrict_mkst_fx. unfold ex_br_ss.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; exact I].
Qed.
End en.

(* ------------------------------------------------------------------ *)
(* 3. The piece                                                         *)
(* ------------------------------------------------------------------ *)

Section x. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.

Theorem ex_braid_ok : ex_braid_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold ex_braid_stmt.
intros HCELLS LAWS _ _ LEAF cx W' c' HBASE _ H978.
unfold ex_st_978 in H978.
destruct H978 as (fx' & ly' & S' & regs' & mem' & md' & res & upb & -> & Hfrm & HCORE & HPERM & Hres4 & Hupb4 &
  HMLE & HMOK & HFR & R18 & R20 & R22 & R23 & HUP & GRES & GUPB & HFSH).
destruct HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1b & Hsp1al & Rgp & Rtp & HSAV & HF4096 & HFal & HFpres & HFL &
  HPAYb & HPAYg).
unfold dec_a_base, dec_lib_pre_x in HBASE.
(* dec_lib_pre_x by type, never by position *)
assert (Hnl : d_n cx = Z.of_nat (length (d_pl cx))) by (decompose [and] HBASE; assumption).
clear HBASE.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hstkv : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
unfold dec_a_saved in HSAV.
(* the geometry of the accepted upstream decode *)
destruct (ex_up_geom _ _ _ _ HUP) as (w & Hlenw & Hwev & Hwr & Hupn & Hupr).
assert (Hw2 : w mod 2 = 0) by (rewrite Zmod_even, Hwev; reflexivity).
assert (Huo : ex_uolen cx = 36 * w).
{ unfold ex_uolen. rewrite Hupr. unfold dec_a_uolen.
  replace (0 <? w) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
assert (Hbl : Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx)) by (unfold d_body; apply ex_body_len; exact Hnl).
assert (Hsp1r : 2 ^ 46 <= d_sp1 cx <= 2 ^ 47) by lia.
assert (Hlow : alloc_ceiling + 4096 <= d_sp1 cx) by lia.
(* the two blocks the call reads *)
assert (InR : In (res, dec_a_len (d_n cx)) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app. right.
  cbn [app In]. left. reflexivity. }
assert (InU : In (upb, ex_uolen cx) (ablocks B ly' S')).
{ apply (Permutation_in _ (Permutation_sym HPERM)). unfold ex_blocks. apply in_or_app. right.
  cbn [app In]. right. left. reflexivity. }
(* the fake frame lies below alloc_ceiling *)
assert (HinF : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (HFaddr : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds segs B LAWS ly' S' W' mem' md' DEC_FCLASS (d_fpos cx) HAR HinF) as (_ & HFceil & _).
rewrite HFaddr in HFceil. change (fs_frame_bytes DEC_FCLASS) with 64 in HFceil.
(* +0x978 .. +0x984 and the jal at +0x988 *)
pose proof (ex_br_entry (fx := fx') W' regs' mem') as HS.
assert (HEI : img_env (@pa_val _ decode_listing PI_decode) A_LIM (EBR regs')) by apply Eimg_env.
assert (SHOK : sh_ok (@pa_segs _ decode_listing PI_decode) (SOff 32 0) (@nil shent) (EBR regs')
  (mrestrict (w_H W') mem')) by constructor.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EBR regs') n = YK11.getr regs' r)
  by (intros nn r Hn; unfold EBR; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (paj_run (fx := fx') (rc := rc) (SK := dec_A_sink_head) (PI := PI_decode) B LAWS) as RUN.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr (@pa_segs _ decode_listing PI_decode) Wx
    (mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 0x978)) mem'
      (YK11.seg_rom (@pa_segs _ decode_listing PI_decode))) md') Q) end.
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0q fp b0 bc lyq ownq) end.
  awr_ro_rec. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in *; clearbody md1 end.
(* the run wrote nothing *)
assert (KM : forall x, ms_mem ms x = mem' x).
{ intros x. lazymatch goal with HFm : frame_of _ _ mem' (ms_mem ms) |- _ => apply HFm end.
  intros (rg & Hin & _). vm_compute in Hin. destruct Hin. }
assert (KR0 : forall a, aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
{ intros a. unfold aview, mbyte, mrestrict. cbv beta. rewrite KM. reflexivity. }
(* the registers at the call *)
reg_at HS (1%bv : bv 5) (Z_to_bv 64 (@pa_val _ decode_listing PI_decode A_TEXT + 2444)) Q1
  ltac:(apply codeptr_val; assumption).
reg_at HS (10%bv : bv 5) (w64 (res + 50)) Q10
  ltac:(cbn [sv_denot]; rewrite (EE 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R18).
reg_at HS (11%bv : bv 5) (w64 upb) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R23).
reg_at HS (12%bv : bv 5) (w64 w) Q12
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; rewrite R22, Hupr;
        reflexivity).
reg_at HS (13%bv : bv 5) (w64 12) Q13 ltac:(reflexivity).
reg_at HS (2%bv : bv 5) (YK11.getr regs' 2) Q2
  ltac:(cbn [sv_denot]; rewrite (EE 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (3%bv : bv 5) (YK11.getr regs' 3) Q3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (4%bv : bv 5) (YK11.getr regs' 4) Q4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (8%bv : bv 5) (YK11.getr regs' 8) Q8
  ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (9%bv : bv 5) (YK11.getr regs' 9) Q9
  ltac:(cbn [sv_denot]; rewrite (EE 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (19%bv : bv 5) (YK11.getr regs' 19) Q19
  ltac:(cbn [sv_denot]; rewrite (EE 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (20%bv : bv 5) (YK11.getr regs' 20) Q20
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (21%bv : bv 5) (YK11.getr regs' 21) Q21
  ltac:(cbn [sv_denot]; rewrite (EE 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (23%bv : bv 5) (YK11.getr regs' 23) Q23
  ltac:(cbn [sv_denot]; rewrite (EE 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
reg_at HS (27%bv : bv 5) (YK11.getr regs' 27) Q27
  ltac:(cbn [sv_denot]; rewrite (EE 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
assert (HspR1 : spZ (ms_regs ms) = d_sp1 cx) by (unfold spZ; rewrite Q2; exact Rsp).
(* the braid relation at the call memory (the crt piece's ex_crt_braid) *)
assert (HBR : dec_crt_braid (aview segs (w_H W') (ms_mem ms)) (res + 50) upb w 12).
{ apply (ex_crt_braid (w_H W') (ms_mem ms) res upb (d_body cx) w); [| | lia | exact Hwev | lia].
  - apply (ex_garr8_kept (w_H W') (w_H W') mem' (ms_mem ms) res _); [|exact GRES].
    intros j Hj. apply KR0.
  - rewrite <- Hupn. apply (ex_garr8_kept (w_H W') (w_H W') mem' (ms_mem ms) upb _); [|exact GUPB].
    intros j Hj. apply KR0. }
(* the call: check_braid (res + 50, upb, w, 12) by its leaf contract *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (YK11.mkst ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (YK11.mkst rg (Z_to_bv 64 (decode_sigma DS_check_braid)) mm rom) mdx) Q) end.
eapply SRr_mono.
{ exact (ex_braid_call B LAWS HCELLS fx' (LEAF fx') W' (ms_regs ms) (ms_mem ms) DEC_LLVMF_STK (d_sp0 cx) []
    (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' md1
    (dec_ev_86c + DEC_CRT_EV) (d_sp1 cx - d_sp0 cx) (res + 50) upb w 12 res (dec_a_len (d_n cx)) upb (ex_uolen cx)
    HJ Q10 Q11 Q12 Q13
    ltac:(rewrite HspR1; lia) ltac:(clear - Hsp1al Hsp0al; lia) ltac:(lia) ltac:(rewrite Hes, Hstkv; lia)
    ltac:(rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_decode)); [lia | reflexivity])
    ltac:(rewrite Q3; exact Rgp) ltac:(rewrite Q4; exact Rtp)
    ltac:(lia) ltac:(lia) InR ltac:(lia) ltac:(clear - Hw2 Hlenw; lia) InU ltac:(lia) ltac:(rewrite Huo; lia)
    HBR). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & Hgr2).
(* what the call kept: every byte outside its stack window [sp1 - ESTACK, sp1) *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx) ->
  aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha Hn. rewrite (HK2 a Ha) by (rewrite HspR1, Hes; exact Hn). apply KR0. }
assert (KL : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W') mem2 a = aview segs (w_H W') mem' a).
{ intros a Ha. apply KA; lia. }
unfold ex_st_98c.
exists fx', ly', S', regs2, mem2, md2, (dec_ev_86c + DEC_CRT_EV), res, upb.
split; [rewrite Q1; reflexivity|].
split; [exact Hfrm|].
split.
{ split; [exact HJ2|].
  split; [exact Hfrs|].
  split; [transitivity (YK11.getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | rewrite Q8; exact R8]|].
  split; [transitivity (YK11.getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | rewrite Q9; exact R9]|].
  split; [unfold spZ at 1; transitivity (bv_unsigned (YK11.getr (ms_regs ms) 2));
    [f_equal; exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact HspR1]|].
  split; [exact Hsp1b|]. split; [exact Hsp1al|].
  split; [transitivity (YK11.getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | rewrite Q3; exact Rgp]|].
  split; [transitivity (YK11.getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | rewrite Q4; exact Rtp]|].
  split.
  { unfold dec_a_saved. apply Forall_forall. intros o Ho.
    pose proof (ex_saved_at_range o Ho) as Hor.
    rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KA; lia).
    exact (proj1 (Forall_forall _ _) HSAV o Ho). }
  split; [exact HF4096|]. split; [exact HFal|].
  split.
  { intros a Ha. apply Hgr2. destruct (HFpres a Ha) as [Hh (b & Hb)].
    split; [exact Hh|]. exists b. rewrite KM. exact Hb. }
  split; [rewrite (ex_rdword_kept (aview segs (w_H W') mem')) by (intros i Hi; apply KL; lia); exact HFL|].
  split; [exact HPAYb|].
  destruct (Z_lt_le_dec 0 (d_n cx)) as [Hn0 | Hn0].
  - pose proof (HPAYb Hn0) as InP.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR InP) as (_ & HP4096 & HPceil & _).
    assert (Hrq : d_n cx <= req_size (d_n cx)) by (unfold req_size; destruct (Z.eqb_spec (d_n cx) 0); lia).
    apply (ex_garr8_kept (w_H W') (w_H W') mem' mem2 (d_p cx) _); [|exact HPAYg].
    intros j Hj. rewrite length_map, <- Hnl in Hj. apply KL. lia.
  - destruct (d_pl cx) as [|b0 pl0] eqn:Epl; [apply garr8_nil|].
    try rewrite Epl in Hnl. cbn [length] in Hnl. lia. }
split; [lia|].
split; [exact HPERM|].
split; [exact Hres4|]. split; [exact Hupb4|].
split; [exact HMLE|]. split; [exact HMOK|].
split.
{ unfold dec_a_fr in HFR |- *. destruct HFR as (F19 & F21 & F27).
  split; [transitivity (YK11.getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | rewrite Q19; exact F19]|].
  split; [transitivity (YK11.getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | rewrite Q21; exact F21]|].
  transitivity (YK11.getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | rewrite Q27; exact F27]. }
split; [transitivity (YK11.getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | rewrite Q20; exact R20]|].
split; [transitivity (YK11.getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | rewrite Q23; exact R23]|].
assert (KSH : forall i, 0 <= i < 8 ->
  aview segs (w_H W') mem2 (d_SH cx + i) = aview segs (w_H W') mem' (d_SH cx + i)).
{ intros i Hi. apply KL. unfold d_SH, shadow_addr, SHADOW_OFF. lia. }
unfold dec_a_fsh in HFSH |- *. destruct HFSH as (L1 & L4 & L5 & L6).
split; [intros i Hi; rewrite KSH by lia; exact (L1 i Hi)|].
split; [rewrite KSH by lia; exact L4|].
split; [rewrite KSH by lia; exact L5|].
intros i Hi; rewrite KSH by lia; exact (L6 i Hi).
Qed.

End x.
