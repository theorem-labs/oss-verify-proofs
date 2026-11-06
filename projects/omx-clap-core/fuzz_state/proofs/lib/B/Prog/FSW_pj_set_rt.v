(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (fs.asan-ubsan) composition of grow's walk (FSW_grow.v's stage lemmas)
   through its two fuzz_realloc calls: grow_holds : grow_spec (lib/B/FSH_Fn_reader.v:575). rule 24 line, reuse search and
   port source: FSW_grow.v's header (lane brief (internal path), CONFIRM a Theorem Labs lane;
   ported from a working branch 75e39a1f41d:proofs/omx-clap-core/fuzz_state/lib/B/Prog/grow.v).
   The callee contract is ALLOC's fuzz_realloc_spec (lib/B/FSH_Fn_alloc.v, CTX-free, the text of S0
   a working branch f32db4da382), the named Section hypothesis fuzz_realloc_holds; the image fact is
   FsShadowSyms B (the shadow-base cells; FSW_grow.v's stages). The theorem's shape mirrors image A's
   (grow_holds : forall {fx rc SK} B, FsShadowSyms B -> fuzz_realloc_spec tfibsegs B -> grow_spec tfibsegs B), with
   tfibsegs B's image (lib/B/YB1v.v, AsanUbsan's loaded segments); grow_spec's Section hypothesis IMG (fs_img_facts) is not
   needed by this walk, so it is not a premise.
   PORTED lemma by lemma (copied, never Required, never bridged), from the image-A walk of the same C, final at
   a working branch 728177ca53c lib/A/Prog/FSW_grow_holds.v (a Theorem Labs lane; its lines 1-501 equal 582c4d69613's):
     fs_pstat_img, grow_frame_chunks (frame 96, s9), gB_rs_ok / gB_disj (shadow cell of v + 24 at atom 25 = s9),
     gC_rs_ok / gC_disj (frame 96), grow_bb, grow_rsum_app, grow_rsum_perm, grow_garr8_ex, grow_mbyte_eq, grow_val_eq,
     grow_writable_grows, fs_pstat_not_ro (B's static addresses 0xa41c0 / 0x5daac0 .. 0x5dab08), grow_perm_swap,
     grow_blk_nodup, grow_block_bytes, grow_v_off_rblk, grow_pj_rw, grow_awr, grow_hdr_upd, grow_glob_img,
     grow_arodata_img, grow_rblock_eq, grow_pobj_run, grow_realloc_step, grow_inFP_blk, grow_val_eqm, grow_moved,
     grow_word_eq, grow_req, ghide, grow_cap_arm (B: frame 96, resumes 0x83d68 / 0x83db8, s9 = the shadow of v + 24,
     the kept registers 3 4 18 26 27) and grow_holds;
   and, for B's own code, from a working branch 75e39a1f41d lib/B/Prog/grow.v: the realloc arms' shape
   (gr_oom_seg / gr_keys_oom_seg are dead here: grow_spec's quiet makes every fuzz_realloc grant, and the resumed a0's
   fact decides the OOM beqz 0x83d6c / 0x83db8 not taken) and the size arithmetic gr_cap2 / gr_sz. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_grow_holds.v, with its module names and numbers changed; 305 of its 365 lines of code are new or changed and 1254 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/Prog/FSW_pj_set_rt.v (a working branch
   e45b7c0a2da, taken there from a working branch 856734bcd0f): the same lemmas, relocated to image B (the
   memcpy call 0x83b30 resuming at 0x83b34 = stage E's ss_pE0, the memset call 0x83b40 resuming at 0x83b44 = stage F's
   ss_pF0; read from image B), over the runtime interface RT_memcpy / RT_memset as A (fr_memcpy / fr_memset, B's
   PC_memcpy 0x51d90 / PC_memset 0x5222c; owner's ruling a Theorem Labs lane: A's hypothesis list exactly); the Section
   binds the sink head explicitly and every statement passes it with @ (owner rule, a Theorem Labs lane). *)
(* pj_set's two RUNTIME calls (fs.asan-ubsan, pj_set 0x83adc): __asan_memcpy (dst, src, 56) at 0x83b30, resuming at
   0x83b34 (stage E's entry, ss_pE0), and __asan_memset (val, 0, 56) at 0x83b40, resuming at 0x83b44 (stage F's entry,
   ss_pF0). Each lemma takes the runtime contract (FSH_Rt.v FsRt fr_memcpy / fr_memset, FSupoisonU.aintrin_realizesU), puts the
   caller's journal back on the memory after the call (FSW_K.fsw_intrin_atU) and builds the resume state
   (FSW_rres.fsw_resume_after_rtU_args, FSW_ret's fss_retT at pj_set's 48-byte frame). For a Theorem Labs lane's composition
   lib/B/Prog/FSW_pj_set_holds.v; it does NOT import that file (cycle), so the two frame
   helpers pS_frame_chunks / pS_ret_disj are carried here as pSr_frame_chunks / pSr_ret_disj (same statements, same
   proofs). The destination / source facts the contract asks are read off AR's block and frame laws over the
   unpoisoned memory and carried to the machine's memory: a block or frame byte is no shadow byte (FSW_rd
   fsw_unpoison_app), and a shadow cell of the user-poisoned heads U reads 0xf7, never None (FSupoison.upoisoned).
   A pobj in a FAKE FRAME is not aowned: AR_frames_law gives ~ aowned for every byte of a live frame.
   rule 24: pj_set proved new on image B (a Theorem Labs lane's lookup, CONFIRM 05:5xZ). A lemma file: no function contract
   is proved here. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_pj FSW_K3 FSW_rd FSW_rres FSPstat FSH_Fn_reader FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_pj_set_tbl FSW_pj_set.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head).
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
(* the runtime interface: __asan_memcpy / __asan_memset at this build's PC_memcpy / PC_memset *)
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis RT_memset : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.

(* ---- the frame helpers (FSW_pj_set_holds.v pS_frame_chunks / pS_ret_disj, verbatim) ---- *)
(* the saved-register chunks of pj_set's frame, from pj_set_frame, under any env whose xatoms 9..14 hold them *)
Lemma pSr_frame_chunks : forall regs2 xs m sp regs,
  firstn 6 (skipn 9 xs) = map (YK11.getr regs) pj_set_saved_regs -> pj_set_frame m sp regs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) m (sp - 48)) pS_cs.
Proof.
intros regs2 xs m sp regs HX Hfr.
assert (EX : forall i, (i < 6)%nat -> ew (Ereg regs2 (fs_extraT ++ xs)) (xatom (9 + i)) =
  nth i (map (YK11.getr regs) pj_set_saved_regs) (Z_to_bv 64 0)).
{ intros i Hi. rewrite fsw_ew_xatom, <- fpj_nth_skipn, <- HX. symmetry. exact (fpj_nth_firstn _ 6 i _ Hi). }
unfold pj_set_frame, pj_set_saved in Hfr.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *. unfold pS_cs.
repeat (apply Forall_cons; [
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff (xatom ?j) 0))) =>
    let i := eval vm_compute in (j - 9)%nat in
    let r := eval vm_compute in (nth i pj_set_saved_regs 0%bv) in
    apply (chunk_ok_val tfibsegs _ _ _ off 8 _ (bv_unsigned (YK11.getr regs r)));
    [ rewrite fsw_SOff0; change j with (9 + i)%nat; rewrite (EX i ltac:(lia)); symmetry; apply Z_to_bv_bv_unsigned
    | apply u64_range | cbn; lia
    | replace (sp - 48 + off) with (sp + (off - 48)) by lia; assumption ] end|]).
apply Forall_nil.
Qed.
(* fsT_ret_regions at pj_set's frame is pairwise disjoint *)
Lemma pSr_ret_disj : forall E sp rs, bv_unsigned (ew E 2) = sp - 48 -> alloc_ceiling + 48 <= sp ->
  rs = [] -> pairwise_disjoint E (fsT_ret_regions 48 pS_cs rs).
Proof.
intros E sp rs E2 Hc ->. pose proof asan_consts as (C1 & _).
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region. cbn [app pairwise_disjoint all_disjoint].
unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* ---- where a 56-byte object of the call lies: inside a live heap block, or inside a live fake frame ---- *)
Definition pSr_in (ly : alayout) (S : astate) (v : Z) : Prop :=
  (exists p nn, In (p, nn) (ablocks B ly S) /\ p <= v /\ v + 56 <= p + req_size nn) \/
  (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= v /\
     v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid).
(* a pobj lies so, and its bytes are addressable on its memory *)
Lemma pSr_pobj : forall ly S (W : world tfibsegs) mem v, pobj tfibsegs B ly S W mem v ->
  pSr_in ly S v /\ range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56.
Proof.
intros ly S W mem v ([((cid & pos & Hin & _ & _ & H1 & H2) & _ & Hr)|((b & nn & Hin & H1 & H2) & _ & Hr)] & _).
- split; [|exact Hr]. right. exists cid, pos. split; [exact Hin|]. split; [exact H1 | exact H2].
- split; [|exact Hr]. left. exists b, nn. split; [exact Hin|]. unfold HEAD in H1. split; [lia | exact H2].
Qed.
(* a shadow hull visible on the unpoisoned memory is visible on the machine's: a cell of a user-poisoned head reads
   0xf7 there (FSupoison.upoisoned), any other cell is the same on both *)
Lemma pSr_hull_raw : forall (W : world tfibsegs) U mem x n, upoisoned tfibsegs W mem U ->
  0 <= x -> x + n <= 2 ^ 63 -> 0 < n ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros W U mem x n HP Hx Hxn Hn Hh s Hs.
assert (Rs : 0 <= s < 2 ^ 64) by (unfold shadow_addr, SHADOW_OFF in Hs; Z.div_mod_to_equations; lia).
destruct (in_ush U (bv_unsigned (Z_to_bv 64 s))) eqn:EU.
- rewrite (wz s Rs) in EU. rewrite (HP s EU). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem s EU). exact (Hh s Hs).
Qed.
(* a byte off the shadow present on the unpoisoned memory is present on the machine's *)
Lemma pSr_present_raw : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44) ->
  apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros ly S U W mem md a HARU Ha Hns (Hh & b & Hb). split; [exact Hh|]. exists b.
rewrite <- (fsw_unpoison_app B ly S U W mem md a HARU Ha Hns). exact Hb.
Qed.
(* the facts the intrinsic contract asks of such an object, on the machine's memory *)
Lemma pSr_obj_facts : forall ly S U (W : world tfibsegs) mem md v,
  ARU tfibsegs B ly S U W mem md -> pSr_in ly S v ->
  4096 <= v /\ v + 56 <= alloc_ceiling /\ amem_range v 56 /\
  (forall a, v <= a < v + 56 -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) v 56.
Proof.
intros ly S U W mem md v HARU Hv.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (proj1 HARU) as HAR. pose proof asan_consts as (C1 & _).
pose proof ASAN_CEIL_range as [CR _].
destruct Hv as [(p & nn & Hin & H1 & H2)|(cid & pos & Hin & H1 & H2)].
- destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p nn HAR Hin) as (_ & H4096 & Hc & _ & Hb & _).
  split; [lia|]. split; [lia|].
  split; [exact (amem_range_of_block tfibsegs B LAWS ly S W (unpoison U mem) md p nn v 56 HAR Hin H1 H2)|].
  split.
  + intros a Ha. destruct (Hb a ltac:(lia)) as (Hp & Hno). split; [|exact Hno].
    apply (pSr_present_raw ly S U W mem md a HARU); [lia | | exact Hp].
    exact (fsw_ablock_off_shadow B ly S W (unpoison U mem) md p nn HAR Hin a ltac:(lia)).
  + apply (pSr_hull_raw W U mem v 56 (proj2 (proj2 HARU))); [lia | lia | lia |].
    exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison U mem) md p nn v 56 HAR Hin H1 H2 ltac:(lia)).
- destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (_ & Happ & Hb & _).
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (F1 & F2 & _).
  split; [lia|]. split; [lia|].
  split.
  { unfold amem_range. destruct Happ as [_ [Hlow | [Hh1 Hh2]]].
    - left. unfold kLowShadowBeg, kLowMemEnd in *. lia.
    - right. unfold kHighMemEnd in *. lia. }
  split.
  + intros a Ha. destruct (Hb a ltac:(lia)) as (Hp & Hno). split; [|exact Hno].
    apply (pSr_present_raw ly S U W mem md a HARU); [lia | | exact Hp].
    pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Hx. unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  + apply (pSr_hull_raw W U mem v 56 (proj2 (proj2 HARU))); [lia | lia | lia |].
    exact (fsw_afobj_hull B ly S W (unpoison U mem) md cid pos v 56 HAR Hin H1 H2 ltac:(lia)).
Qed.

(* ---- the return of a runtime call made at pj_set's frame (sp = sp0 - 48) that writes [dst, dst + 56) and its own
   stack window below sp: the journal put back on the memory after the call, and the resume state fss_retT r at the
   return address r, with the call's own fact P on the new memory ---- *)
Lemma pSr_rt_resume : forall lyE SE UE (WE : world tfibsegs) memE mdE ly2 S2 U2 (W2 : world tfibsegs) memC mdC
    (FP : list (Z * Z)) (sp0 kc : Z) (regs regsC : bvmap 5 word) (cnt fail live peak ty kids keys n cap dst r : Z)
    (P : (word -> option byte) -> Prop) (c0 : config) (Q : world tfibsegs -> config -> Prop),
  @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
    ly2 S2 W2 (unpoison U2 memC) mdC kc ->
  spZ regsC = sp0 - 48 -> raZ regsC = r -> dst + 56 <= alloc_ceiling ->
  (forall a, dst <= a < dst + 56 ->
     awr_byte tfibsegs B STK_pj_set sp0 FP (ablocks B lyE SE) (ablocks B ly2 S2) ly2 [] (frames SE) a) ->
  pj_set_frame (mrestrict (w_H W2) memC) sp0 regs ->
  SRr tfibsegs W2 c0
    (fun W' c' => W' = W2 /\ exists regs' mem' md',
       c' = YG0d.cfg_at tfibsegs (raZ regsC) regs' mem' md' /\
       ARU tfibsegs B ly2 S2 U2 W2 mem' md' /\ same_but_materialized mdC md' /\ aregs_preserved regsC regs' /\
       P mem' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + 56) -> ~ (spZ regsC - ESTACK <= a < spZ regsC) ->
          aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a) /\
       (forall a, apresent (w_H W2) memC a -> apresent (w_H W2) mem' a)) ->
  (forall regs' mem' md',
     @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
       ly2 S2 W2 (unpoison U2 mem') md' kc ->
     ARU tfibsegs B ly2 S2 U2 W2 mem' md' ->
     aregs_preserved regsC regs' ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs))
       (fss_retT r 48 pS_cs [] [])
       (restrict (w_H W2) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     P mem' ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (dst <= x < dst + 56) ->
        ~ (sp0 - 48 - ESTACK <= x < sp0 - 48) ->
        aview tfibsegs (w_H W2) mem' x = aview tfibsegs (w_H W2) memC x) ->
     (forall x, apresent (w_H W2) memC x -> apresent (w_H W2) mem' x) ->
     SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W2 c0 Q.
Proof.
intros lyE SE UE WE memE mdE ly2 S2 U2 W2 memC mdC FP sp0 kc regs regsC cnt fail live peak ty kids keys n cap dst r
  P c0 Q HJ Hsp Hra Hdc HWR Hfr HC KB.
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (SE48 : ESTACK + 48 <= STK_pj_set) by (vm_compute; congruence).
assert (EST : ESTACK = 4096) by reflexivity.
assert (S48 : 48 <= STK_pj_set) by lia.
assert (Hc48 : alloc_ceiling + 48 <= sp0) by lia.
(* the call, the journal put back on the memory after it *)
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE [] ly2 S2 U2 W2 memC mdC kc U2
    (fun a => dst <= a < dst + 56 \/ spZ regsC - ESTACK <= a < spZ regsC) (w64 (raZ regsC)) c0
    (fun regs' mem' md' => aregs_preserved regsC regs' /\ P mem' /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (dst <= a < dst + 56) -> ~ (spZ regsC - ESTACK <= a < spZ regsC) ->
          aview tfibsegs (w_H W2) mem' a = aview tfibsegs (w_H W2) memC a) /\
       (forall a, apresent (w_H W2) memC a -> apresent (w_H W2) mem' a)) HJ).
  - eapply SRr_mono; [exact HC|].
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & Hsame & HP' & HPm & Hfr' & Hpr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|].
    split.
    { intros a Ha HnW.
      destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
      - apply (aview_unpoison_in tfibsegs). exact EU.
      - rewrite !(aview_unpoison_out tfibsegs) by exact EU.
        apply Hfr'; [exact Ha | intros Hx; apply HnW; left; exact Hx | intros Hx; apply HnW; right; exact Hx]. }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|].
      destruct (in_ush U2 (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
      - exists (Z_to_bv 8 0). apply unpoison_in. exact EU.
      - rewrite (unpoison_out U2 mem' (Z_to_bv 64 a) EU). rewrite (unpoison_out U2 memC (Z_to_bv 64 a) EU) in Hb.
        destruct (Hpr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP'|]. split; [exact HPm|]. split; [exact Hfr' | exact Hpr].
  - intros a [Ha | Ha].
    + exact (HWR a Ha).
    + left. left. rewrite Hsp in Ha. lia. }
cbv beta. intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP & HPm & HFR & HPR).
(* ---- the resume at r ---- *)
assert (ERA : w64 (raZ regsC) = Z_to_bv 64 r) by (rewrite Hra; reflexivity).
rewrite ERA.
set (xs := pj_xs cnt fail live peak ty kids keys n cap regs) in *.
assert (HX : firstn 6 (skipn 9 xs) = map (YK11.getr regs) pj_set_saved_regs)
  by (unfold xs, pj_xs, pj_fields, pj_set_saved_regs; cbn; reflexivity).
assert (E2 : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ xs)) 2) = sp0 - 48).
{ rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl).
  rewrite (fsw_pres _ _ 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Hsp. }
assert (KEEP : forall a, sp0 - 48 <= a < sp0 ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) a = mbyte tfibsegs (mrestrict (w_H W2) memC) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply HFR; [lia | lia | rewrite Hsp; lia]. }
assert (CHK : Forall (YP09.chunk_ok tfibsegs (Ereg regs2 (fs_extraT ++ xs)) (mrestrict (w_H W2) memC) (sp0 - 48)) pS_cs)
  by exact (pSr_frame_chunks regs2 xs _ sp0 regs HX Hfr).
assert (CIN : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 48) pS_cs)
  by (repeat constructor; cbn; lia).
assert (WF : regions_wf (fsT_ret_regions 48 pS_cs []) = true) by (vm_compute; reflexivity).
assert (PD : pairwise_disjoint (Ereg regs2 (fs_extraT ++ xs)) (fsT_ret_regions 48 pS_cs []))
  by exact (pSr_ret_disj _ sp0 [] E2 Hc48 eq_refl).
apply (KB regs2 mem2 md2 HJ2 HARU2 HP).
- exact (fsw_resume_after_rtU_args B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE [] ly2 S2 U2 W2 mem2 md2 kc
    regsC regs2 memC 48 xs pS_cs [] [] r (proj1 HSS) (proj2 HSS) HJ2 HARU2 HP Hsp ltac:(lia) S48 eq_refl WF CIN CHK
    KEEP (Forall_nil _) PD I).
- exact HPm.
- intros x H1 H2 H3. apply HFR; [exact H1 | exact H2 | rewrite Hsp; exact H3].
- exact HPR.
Qed.

(* ---- the call of __asan_memcpy (dst, src, 56) at 0x83b30 (ra 0x83b34): dst inside a live block past its head, src a
   pobj, the two apart; through to stage E's resume state ss_pE0 at 0x83b34 ---- *)
Lemma pS_memcpy_call : forall lyE SE UE (WE : world tfibsegs) memE mdE
    ly2 S2 U2 (W2 : world tfibsegs) memC mdC (FP : list (Z * Z)) (sp0 kc : Z)
    (regs regsC : bvmap 5 word) (cnt fail live peak ty kids keys n cap dst src : Z)
    (Q : world tfibsegs -> config -> Prop),
  @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
    ly2 S2 W2 (unpoison U2 memC) mdC kc ->
  ARU tfibsegs B ly2 S2 U2 W2 memC mdC ->
  FSupoisonU.fs_heads B ly2 S2 U2 ->
  spZ regsC = sp0 - 48 -> sp0 = spZ regs ->
  YK11.getr regsC 1 = w64 0x83b34 ->
  YK11.getr regsC 10 = w64 dst -> YK11.getr regsC 11 = w64 src -> YK11.getr regsC 12 = w64 56 ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  (exists p nn, In (p, nn) (ablocks B ly2 S2) /\ p + HEAD <= dst /\ dst + 56 <= p + req_size nn) ->
  pobj tfibsegs B ly2 S2 W2 memC src ->
  (dst + 56 <= src \/ src + 56 <= dst) ->
  (forall a, dst <= a < dst + 56 ->
     awr_byte tfibsegs B STK_pj_set sp0 FP (ablocks B lyE SE) (ablocks B ly2 S2) ly2 [] (frames SE) a) ->
  pj_set_frame (mrestrict (w_H W2) memC) sp0 regs ->
  (forall regs' mem' md',
     @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
       ly2 S2 W2 (unpoison U2 mem') md' kc ->
     ARU tfibsegs B ly2 S2 U2 W2 mem' md' ->
     aregs_preserved regsC regs' ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) ss_pE0
       (restrict (w_H W2) (mkst regs' (Z_to_bv 64 0x83b34) mem' (seg_rom tfibsegs))) ->
     (forall i, 0 <= i < 56 ->
        aview tfibsegs (w_H W2) mem' (dst + i) = aview tfibsegs (w_H W2) memC (src + i)) ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (dst <= x < dst + 56) ->
        ~ (sp0 - 48 - ESTACK <= x < sp0 - 48) ->
        aview tfibsegs (w_H W2) mem' x = aview tfibsegs (w_H W2) memC x) ->
     (forall x, apresent (w_H W2) memC x -> apresent (w_H W2) mem' x) ->
     SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 0x83b34) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs PC_memcpy regsC memC mdC) Q.
Proof.
intros lyE SE UE WE memE mdE ly2 S2 U2 W2 memC mdC FP sp0 kc regs regsC cnt fail live peak ty kids keys n cap dst src Q
  HJ HARU FH Hsp Hsp0 R1 R10 R11 R12 R3 R4 (p & nn & Hin & Hd1 & Hd2) HPS HDJ HWR Hfr KB.
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (SE48 : ESTACK + 48 <= STK_pj_set) by (vm_compute; congruence).
assert (EST : ESTACK = 4096) by reflexivity.
(* the destination (a block body) and the source (a pobj) *)
assert (DIN : pSr_in ly2 S2 dst).
{ left. exists p, nn. split; [exact Hin|]. unfold HEAD in Hd1. split; [lia | exact Hd2]. }
destruct (pSr_obj_facts ly2 S2 U2 W2 memC mdC dst HARU DIN) as (D1 & D2 & DAM & DPR & DHULL).
destruct (pSr_pobj ly2 S2 W2 memC src HPS) as (SIN & SRA).
destruct (pSr_obj_facts ly2 S2 U2 W2 memC mdC src HARU SIN) as (X1 & X2 & XAM & XPR & XHULL).
(* the call's premises *)
assert (HPRE : ecall_preU tfibsegs B ly2 S2 U2 W2 regsC memC mdC).
{ refine (fsw_ecall_preU_at B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE [] ly2 S2 U2 W2 memC mdC kc regsC (-48)
    HJ HARU _ eq_refl _ _ _ R3 R4).
  - lia.
  - lia.
  - lia.
  - rewrite R1. apply ret_ok_even. vm_compute. reflexivity. }
assert (HDEST : dest_ok tfibsegs B ly2 S2 W2 regsC memC dst 56).
{ intros a Ha. destruct (DPR a Ha) as (Hpa & Hno).
  split; [exact (apresent_writable tfibsegs _ _ _ Hpa)|]. split; [exact Hno|]. rewrite Hsp. lia. }
assert (HRAd : range_addressable (aview tfibsegs (w_H W2) memC) SHADOW_OFF dst 56).
{ apply (fsw_block_body_addressable B ly2 S2 U2 W2 memC mdC p nn dst 56 HARU FH Hin); [unfold HEAD in Hd1; lia | lia | exact Hd2]. }
assert (HSRC : src_ok tfibsegs W2 regsC memC src 56).
{ intros a Ha. destruct (XPR a Ha) as (Hpa & _).
  split; [exact (aview_some_of_apresent tfibsegs _ _ _ Hpa)|]. rewrite Hsp. lia. }
assert (HCPY : 0 <= src /\ src + 56 <= 2 ^ 63 /\ src_ok tfibsegs W2 regsC memC src 56 /\
  (dst + 56 <= src \/ src + 56 <= dst) /\ amem_range src 56 /\
  range_addressable (aview tfibsegs (w_H W2) memC) SHADOW_OFF src 56 /\
  (0 < 56 -> shadow_hull_vis (aview tfibsegs (w_H W2) memC) src 56)).
{ split; [lia|]. split; [lia|]. split; [exact HSRC|]. split; [exact HDJ|]. split; [exact XAM|].
  split; [exact SRA | intros _; exact XHULL]. }
assert (ERA : raZ regsC = 0x83b34) by (unfold raZ; rewrite R1; vm_compute; reflexivity).
apply (pSr_rt_resume lyE SE UE WE memE mdE ly2 S2 U2 W2 memC mdC FP sp0 kc regs regsC cnt fail live peak ty kids keys
  n cap dst 0x83b34
  (fun mem' => forall i, 0 <= i < 56 -> aview tfibsegs (w_H W2) mem' (dst + i) = aview tfibsegs (w_H W2) memC (src + i))
  _ Q HJ Hsp ERA D2 HWR Hfr); [|exact KB].
eapply SRr_mono.
{ exact (RT_memcpy ly2 S2 U2 W2 regsC memC mdC dst src 56 HPRE R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) HDEST DAM HRAd (fun _ => DHULL) HCPY). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & _ & Hcp & Hfr' & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|]. split; [exact HP'|].
split; [exact Hcp|]. split; [exact Hfr' | exact Hpr].
Qed.

(* ---- the call of __asan_memset (val, 0, 56) at 0x83b40 (ra 0x83b44): val a pobj (a fake-frame object or a heap
   kid); through to stage F's resume state ss_pF0 at 0x83b44 ---- *)
Lemma pS_memset_call : forall lyE SE UE (WE : world tfibsegs) memE mdE
    ly2 S2 U2 (W2 : world tfibsegs) memC mdC (FP : list (Z * Z)) (sp0 kc : Z)
    (regs regsC : bvmap 5 word) (cnt fail live peak ty kids keys n cap dst : Z)
    (Q : world tfibsegs -> config -> Prop),
  @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
    ly2 S2 W2 (unpoison U2 memC) mdC kc ->
  ARU tfibsegs B ly2 S2 U2 W2 memC mdC ->
  FSupoisonU.fs_heads B ly2 S2 U2 ->
  spZ regsC = sp0 - 48 -> sp0 = spZ regs ->
  YK11.getr regsC 1 = w64 0x83b44 ->
  YK11.getr regsC 10 = w64 dst -> YK11.getr regsC 11 = w64 0 -> YK11.getr regsC 12 = w64 56 ->
  YK11.getr regsC 3 = w64 (as_gp B) -> YK11.getr regsC 4 = w64 (as_tp B) ->
  pobj tfibsegs B ly2 S2 W2 memC dst ->
  (forall a, dst <= a < dst + 56 ->
     awr_byte tfibsegs B STK_pj_set sp0 FP (ablocks B lyE SE) (ablocks B ly2 S2) ly2 [] (frames SE) a) ->
  pj_set_frame (mrestrict (w_H W2) memC) sp0 regs ->
  (forall regs' mem' md',
     @ajournal rc SK tfibsegs B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE []
       ly2 S2 W2 (unpoison U2 mem') md' kc ->
     ARU tfibsegs B ly2 S2 U2 W2 mem' md' ->
     aregs_preserved regsC regs' ->
     st_ok tfibsegs (Ereg regs' (fs_extraT ++ pj_xs cnt fail live peak ty kids keys n cap regs)) ss_pF0
       (restrict (w_H W2) (mkst regs' (Z_to_bv 64 0x83b44) mem' (seg_rom tfibsegs))) ->
     (forall i, 0 <= i < 56 -> aview tfibsegs (w_H W2) mem' (dst + i) = Some 0) ->
     (forall x, 0 <= x < 2 ^ 64 -> ~ (dst <= x < dst + 56) ->
        ~ (sp0 - 48 - ESTACK <= x < sp0 - 48) ->
        aview tfibsegs (w_H W2) mem' x = aview tfibsegs (w_H W2) memC x) ->
     (forall x, apresent (w_H W2) memC x -> apresent (w_H W2) mem' x) ->
     SRr tfibsegs W2 (mkCfg (mkst regs' (Z_to_bv 64 0x83b44) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs PC_memset regsC memC mdC) Q.
Proof.
intros lyE SE UE WE memE mdE ly2 S2 U2 W2 memC mdC FP sp0 kc regs regsC cnt fail live peak ty kids keys n cap dst Q
  HJ HARU FH Hsp Hsp0 R1 R10 R11 R12 R3 R4 HPD HWR Hfr KB.
pose proof asan_consts as (C1 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
assert (SE48 : ESTACK + 48 <= STK_pj_set) by (vm_compute; congruence).
assert (EST : ESTACK = 4096) by reflexivity.
(* the destination: a pobj, in a live fake frame or a live block *)
destruct (pSr_pobj ly2 S2 W2 memC dst HPD) as (DIN & DRA).
destruct (pSr_obj_facts ly2 S2 U2 W2 memC mdC dst HARU DIN) as (D1 & D2 & DAM & DPR & DHULL).
(* the call's premises *)
assert (HPRE : ecall_preU tfibsegs B ly2 S2 U2 W2 regsC memC mdC).
{ refine (fsw_ecall_preU_at B STK_pj_set sp0 FP lyE SE WE (unpoison UE memE) mdE [] ly2 S2 U2 W2 memC mdC kc regsC (-48)
    HJ HARU _ eq_refl _ _ _ R3 R4).
  - lia.
  - lia.
  - lia.
  - rewrite R1. apply ret_ok_even. vm_compute. reflexivity. }
assert (HDEST : dest_ok tfibsegs B ly2 S2 W2 regsC memC dst 56).
{ intros a Ha. destruct (DPR a Ha) as (Hpa & Hno).
  split; [exact (apresent_writable tfibsegs _ _ _ Hpa)|]. split; [exact Hno|]. rewrite Hsp. lia. }
assert (ERA : raZ regsC = 0x83b44) by (unfold raZ; rewrite R1; vm_compute; reflexivity).
apply (pSr_rt_resume lyE SE UE WE memE mdE ly2 S2 U2 W2 memC mdC FP sp0 kc regs regsC cnt fail live peak ty kids keys
  n cap dst 0x83b44
  (fun mem' => forall i, 0 <= i < 56 -> aview tfibsegs (w_H W2) mem' (dst + i) = Some 0)
  _ Q HJ Hsp ERA D2 HWR Hfr); [|exact KB].
eapply SRr_mono.
{ exact (RT_memset ly2 S2 U2 W2 regsC memC mdC dst 0 56 HPRE R10 R11 R12 ltac:(lia) ltac:(lia)
    ltac:(lia) HDEST DAM DRA (fun _ => DHULL) I). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & _ & Hcp & Hfr' & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|]. split; [exact HP'|].
split; [exact Hcp|]. split; [exact Hfr' | exact Hpr].
Qed.
End R.
