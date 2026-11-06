(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30 (G-BRA, B top_x row 21 RA_x): the B top's RA_x at its cf instance.

   fr_relay_add_x is the B top's RA_x (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:220, with the room record RP after MT as
   the room kit's ra_spec_g_x states it, lib/B/W_contract_x.v Section w5g) at B := TfibB, PST := [], ARx := ARX_ra
   (top_x.v:154-155's ARX, the same body), RG := fr_globals, CTX := YCk0.CTX_AREALLOC, from lib/B/W_relay_add_x.v's
   pb_relay_add_x.  Its Section hypotheses are top_x's own texts (TL, TLF, MLAW, FFL, HRO, ALOCK, AUNLOCK, the realloc
   rule at a ceiling MMAX with ATABLE < MMAX), the meter law MO_FR, and two callee laws of the instance the top did not
   state: AMEMSET_x (the memset intrinsic at ARX) and ASM0 (__asan_stack_malloc_0, for wake's class-0 fake frame at
   0x824d0).  Every other walk premise is discharged here: the cf laws as top_x.v:610-648 derives them, wake by
   lib/B/W_wake_x.v pb_wake_x, the placement facts by lib/B/W_relay_add_cut.v Section fr / W_wake_x.v wk_hv8_fr, and
   the image facts by computation at TfibB.  It holds at any meter MT with MLAW and MO_FR (top_x's meter Variable). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d YCbp.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_kit_x W_sites_x W_frame_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_wake_c W_wake_c_x W_relay_add_cut W_relay_add_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_wake_x W_img_x.
(* the instance: TfibB and its start-up facts, the cf relation and its laws, the K0 table *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD2l YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YG0lawscf YGcallcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcallx YG01cf YG05cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YG0tcf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCk0 W_LLVMFuzzerTestOneInput_G.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* ---- THE INSTANCE: the B top's cf relation (lib/B/W_LLVMFuzzerTestOneInput_top_x.v:154-155), TfibB, fr_globals, the K0 realloc table ---- *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* top_x.v:154-155's ARX, the same body: the cf live state with an empty ghost head set *)
Definition ARX_ra : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_B) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [].

Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
(* top_x.v:203-205 TL / TLF / MLAW, :207 FFL, :211 HRO, :304-305 ALOCK / AUNLOCK, :223 ARE_x (the realloc rule, here at any
   ceiling MMAX that admits the table, with the room record RP); MO_FR is the meter law wake's fake frame needs (a
   set_fs costs nothing, KF-COUNT #4's text); ASM0 and AMEMSET_x are the two callee laws the top did not state *)
Hypothesis TL : PALib TfibB.
Hypothesis TLF : PALibF TfibB.
Hypothesis MLAW : ameter_laws MT.
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis FFL : frame_flag_lawP_x segs TfibB ARX_ra.
Hypothesis HRO : rom_out segs TfibB (W_LLVMFuzzerTestOneInput_G.G_fr_c TfibB).
Hypothesis ASM0 : astack_malloc_pres_x segs TfibB ARX_ra 0.
Hypothesis ALOCK : alock_realizes_x (PI := PB_fr) TfibB ARX_ra (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x (PI := PB_fr) TfibB ARX_ra (SIGMA WS_pthread_mutex_unlock).
Hypothesis HMMAX : ATABLE < MMAX.
Hypothesis ARE_x : arealloc_cf_rule_c_x segs TfibB [] ARX_ra MT MMAX RP YCk0.CTX_AREALLOC (SIGMA WS_realloc).
Hypothesis AMEMSET_x : aintrin_realizes_x segs TfibB ARX_ra OSet (SIGMA WS_asan_memset).

Theorem fr_relay_add_x :
  ra_spec_g_x (PI := PB_fr) TfibB [] ARX_ra MT RP fr_globals YCk0.CTX_AREALLOC (BASE + AF_fr_relay_add).
Proof.
  intros G _ _.
  pose proof (ts_errno TfibB TfibB_syms) as HEV.
  (* the cf laws over ARX_ra (top_x.v:156-163, :610-648, the same proofs) *)
  assert (LAWS : AR_laws_x segs TfibB ARX_ra (@cf_head CfParams_reply)).
  { unfold ARX_ra. apply AR_laws_x_and_hp.
    exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)). }
  assert (HP0 : forall ly S Hp (W : world segs) mem md, ARX_ra ly S Hp W mem md -> Hp = [])
    by (intros ly S Hp W mem md H; exact (proj2 H)).
  assert (BLKN : forall ly S Hp (W : world segs) mem md p n, ARX_ra ly S Hp W mem md ->
    In (p, n) (ablocks TfibB ly S) -> 0 <= n).
  { intros ly S Hp W mem md p n H Hin.
    destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB) ly S Hp W mem md p n (proj1 H) Hin)
      as (_ & _ & _ & _ & _ & _ & Hn). lia. }
  assert (OWNLOW : ARx_owned_low_law segs TfibB ARX_ra).
  { intros ly S Hp W mem md a H Ho.
    exact (ARx_owned_low_law_cf_x (cp := CfParams_reply) segs TfibB (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)
      ly S Hp W mem md a (proj1 H) Ho). }
  assert (WFL : ARx_wf_law segs ARX_ra (Wf_cf (cp := CfParams_reply) (as_universe TfibB))).
  { intros ly S Hp W mem md H. exact (ARx_wf_law_cf_x (cp := CfParams_reply) segs TfibB ly S Hp W mem md (proj1 H)). }
  assert (SMALLOC : forall s cid, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> 0 <= cid <= 10 ->
    count_cid cid (frames s) < fs_frames cid ->
    exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
    frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s)).
  { intros s cid HWF Hcid Hcnt.
    destruct (stack_malloc_progress_cf (cp := CfParams_reply) _ s cid HWF Hcid Hcnt) as (pos & s' & Hpath).
    pose proof (stack_malloc_ok_cf (cp := CfParams_reply) _ s cid HWF Hcid) as HTOK.
    destruct (atok_apath _ _ _ [] (PFake cid pos, s') HTOK Hpath) as (ns' & HQ). unfold stack_malloc_post_cf in HQ.
    destruct HQ as (_ & Hf & _ & _ & Hfrs & Hfresh).
    exists pos, s'. split; [exact Hpath|]. split; [exact Hf|]. split; [exact Hfrs | exact Hfresh]. }
  assert (ASF : astack_free_law_x segs TfibB ARX_ra).
  { intros ly S Hp W mem md mem' md' cid pos H Hin HF HO HV Hvm Hlz He HK. unfold ARX_ra in H |- *.
    split; [|exact (proj2 H)].
    exact (YG0tcf.astack_free_law_ok_cf (cp := CfParams_reply) segs TfibB ly S Hp W mem md mem' md' cid pos (proj1 H)
      Hin HF HO HV Hvm Hlz He HK). }
  assert (SFREE : forall s cid pos, Wf_cf (cp := CfParams_reply) (as_universe TfibB) s -> In (cid, pos) (frames s) ->
    exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2).
  { intros s cid pos HWF Hin. exact (proj2 (stack_free_ok_cf (cp := CfParams_reply) _ s cid pos HWF Hin)). }
  assert (IMGC : forall ly S Hp (W : world segs) mem md, ARX_ra ly S Hp W mem md ->
    fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
    by exact (W_img_x.fr_img_cover_x TfibB ARX_ra LAWS).
  assert (HPST : forall a, in_img segs a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
  (* the image facts at TfibB, by computation (W_LLVMFuzzerTestOneInput_G.v's deciders; YF0m's start-up tables) *)
  assert (UNOWN : forall G0 a, forallb (W_LLVMFuzzerTestOneInput_G.rng_all (fun x => negb (existsb
      (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_owned_static))) G0 = true ->
    inG G0 a -> ~ Exists (in_zr a) (as_owned_static TfibB)).
  { intros G0 a Hf Ha Ho. rewrite (ts_owned TfibB TfibB_syms) in Ho.
    pose proof (W_LLVMFuzzerTestOneInput_G.rng_all_in _ G0 a Hf Ha) as Hx. apply negb_true_iff in Hx.
    apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
    assert (Hb : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) Tfib_owned_static = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Hx. discriminate Hx. }
  (* QMm W0': gx_ok's kept clause, as UNOWN over YF0m's Tfib_kept *)
  assert (UNKEPT : forall G0 a, forallb (W_LLVMFuzzerTestOneInput_G.rng_all (fun x => negb (existsb
      (fun r => (fst r <=? x) && (x <? fst r + snd r)) Tfib_kept))) G0 = true ->
    inG G0 a -> ~ Exists (in_zr a) (as_kept TfibB)).
  { intros G0 a Hf Ha Ho. rewrite (ts_kept TfibB TfibB_syms) in Ho.
    pose proof (W_LLVMFuzzerTestOneInput_G.rng_all_in _ G0 a Hf Ha) as Hx. apply negb_true_iff in Hx.
    apply Exists_exists in Ho as (r & Hr & Hz). unfold in_zr in Hz.
    assert (Hb : existsb (fun r => (fst r <=? a) && (a <? fst r + snd r)) Tfib_kept = true).
    { apply existsb_exists. exists r. split; [exact Hr|]. apply andb_true_intro.
      split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    rewrite Hb in Hx. discriminate Hx. }
  assert (INIMG : forall G0 a, forallb (W_LLVMFuzzerTestOneInput_G.rng_all (W_LLVMFuzzerTestOneInput_G.segin segs)) G0 = true ->
    inG G0 a -> in_img segs a).
  { intros G0 a Hf Ha. apply W_LLVMFuzzerTestOneInput_G.segin_ok.
    exact (W_LLVMFuzzerTestOneInput_G.rng_all_in _ G0 a Hf Ha). }
  assert (HG : gx_ok segs TfibB (RA_G fr_globals)).
  { intros a Ha. split.
    - apply (INIMG (RA_G fr_globals) a); [vm_compute; reflexivity | exact Ha].
    - split.
      + apply (UNOWN (RA_G fr_globals) a); [vm_compute; reflexivity | exact Ha].
      + apply (UNKEPT (RA_G fr_globals) a); [vm_compute; reflexivity | exact Ha]. }
  assert (HWK : forall a, rg_wake fr_globals + 4 <= a < rg_wake fr_globals + 8 ->
    in_img segs a /\ ~ Exists (in_zr a) (as_owned_static TfibB) /\ ~ (as_errno TfibB <= a < as_errno TfibB + 4)).
  { intros a Ha.
    assert (HaG : inG [(rg_wake fr_globals + 4, 4)] a) by (apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia).
    split; [apply (INIMG [(rg_wake fr_globals + 4, 4)] a); [vm_compute; reflexivity | exact HaG]|].
    split; [apply (UNOWN [(rg_wake fr_globals + 4, 4)] a); [vm_compute; reflexivity | exact HaG]|].
    rewrite HEV. unfold TFIB_ERRNO. cbn [fr_globals rg_wake] in Ha. lia. }
  assert (HERRS : forall a, as_errno TfibB <= a < as_errno TfibB + 4 -> ~ Exists (in_zr a) (as_owned_static TfibB)).
  { intros a Ha. apply (UNOWN [(TFIB_ERRNO, 4)] a); [vm_compute; reflexivity|].
    apply inG_cons; left; unfold in_zr; cbn [fst snd]. rewrite HEV in Ha. lia. }
  assert (HNROM : forall a, inG (RA_G fr_globals) a -> ~ in_rom segs a) by exact ra_nrom_fr.
  assert (HROMO : rom_out segs TfibB (RA_G fr_globals)).
  { intros a Hr. destruct (HRO a Hr) as (_ & H2 & H3 & H4).
    split; [intros Hin; exact (HNROM a Hin Hr)|]. exact (conj H2 (conj H3 H4)). }
  assert (HHV : pa_val (PAImg := PB_fr) (A_OBJ 3) = rg_lock fr_globals /\ pa_val (PAImg := PB_fr) (A_OBJ 4) = rg_nsrc fr_globals /\
    pa_val (PAImg := PB_fr) (A_OBJ 5) = rg_src fr_globals /\ pa_val (PAImg := PB_fr) (A_OBJ 13) = rg_capsrc fr_globals /\
    pa_val (PAImg := PB_fr) (A_HI 28) + RA_HI_NSRC = rg_nsrc fr_globals /\
    pa_val (PAImg := PB_fr) (A_HI 29) + RA_HI_CAPSRC = rg_capsrc fr_globals /\
    pa_val (PAImg := PB_fr) (A_HI 30) + RA_HI_SRC = rg_src fr_globals) by exact ra_hv_fr.
  destruct HHV as (HV3 & HV4 & HV5 & HV13 & HH28 & HH29 & HH30).
  assert (HRGA : ra_aligned fr_globals) by exact ra_aligned_fr.
  assert (HRGP : ra_apart (ra_cells (PI := PB_fr) fr_globals)) by exact ra_cells_fr.
  assert (HV8 : pa_val (PAImg := PB_fr) (A_OBJ 8) = rg_wake fr_globals) by exact W_wake_x.wk_hv8_fr.
  (* wake over ARX_ra (W_wake_x.v), its class-0 fake frame by ASM0 *)
  assert (WAKE : wk_spec_x (PI := PB_fr) TfibB [] ARX_ra fr_globals (BASE + AF_fr_wake))
    by exact (W_wake_x.pb_wake_x (PI := PB_fr) TfibB [] ARX_ra fr_globals LAWS TL TLF _ WFL SFREE SMALLOC OWNLOW IMGC
      ASM0 ASF FFL HV8 HWK HERRS).
  exact (pb_relay_add_x (PI := PB_fr) TfibB [] ARX_ra MT RP MMAX G fr_globals YCk0.CTX_AREALLOC LAWS HP0 TL MLAW HG HWK
    HNROM HROMO MO_FR HV3 HV4 HV5 HV13 HH28 HH29 HH30 HRGA HRGP HMMAX HPST IMGC BLKN ALOCK AUNLOCK ARE_x AMEMSET_x
    WAKE).
Qed.
End inst.
