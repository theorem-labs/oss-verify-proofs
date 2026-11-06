(* fuzz_preset, image A' (asan 1be0f53d96cb, unstripped twin bff8519bbe3e; #102): the program walk of grow
   (preset_file.c:42-64; 103 instructions) against the kit's announced cut (7cdbb61b5fa0, owner
   06:11Z); its kit texts and engine are those of the cut 7cdbb61b5fa0: tgrow_specX (lib/A/PRH_FnReader.v
   blob f1ae32e3b2cd, :812-1057, the POST-IMPLICATION form), tfuzz_realloc_specX (PRH_FnAlloc 4d8aeba047e5), PRH_Base
   ef7c8ca98529 (fpre carries FRM0-ENTRY; prh_univ_closure without DW; prh_live_evs; prh_cons_from).
   RELOCATED from the old-pin walk (ecde1e0fbcd6, image A asan d83eb25d) by alreloc
   c4338d099cfb8025 (audited AGREE), then RE-FITTED (this lane): the ledger's g_most / g_own_ran_out fields, the
   PST's two new cells, the position as the text's post-implication (each arm moves any position at S by the arm's
   events E), the live requests after each arm (Permutation .. (hlive_from .. E), PwGrowLive.v), the inner calls' live
   counts from the text's pkR premises, the inner calls' live bytes from the text's live room at each event
   (PwGrowLive.grow_room_kids / grow_room_keys), and the refused arms: the callee's refusal ledger verbatim plus the
   OUTCOME exclusion (the leaf's grant clause at a consumer allocation of the all-granted run says the instance
   granted, contradicting the NULL). Its callee fuzz_realloc is tfuzz_realloc_specX, a STATED HYPOTHESIS (HREALLOC)
   until the allocator's S1 walk lands. No AGREE-PREFIX: grow_holds states tgrow_specX EXACTLY.
   THE FREE / REALLOC MOVE: both texts are restated for it (the conclusion at SRr' segs RZ_cf and fpostWmR / fpostmR at
   the world relation wle' segs RZ_cf, the hull budget premise and the hull use, the world-free refusal evidence, the
   guarded exclusion at the kids-refused arm). The walk runs at wle' (lifted once at its top: the R runners
   paj_run_xfR / paj_run_xf_invR / paj_run_to_xf_invR, paj_branchR, aj_call_xW_spR); the kids / keys calls take their
   hull budgets from grow's (PwGrowG.grow_hull_kids / grow_hull_keys) and each return states the hull use; the
   exclusion is PwGrowG.grow_excl_of_leaf of the kids call's OUTCOME; gr_Q / gr_KR are the kit's named posts tgrP_Q / tfrP_Q.
   FORM: cgif's per-function walk form over the CONCRETE listing of the whole target range,
   A_prog_listing with its instances PL_prog_A / PI_prog_A (lib/A/PAImg_prog.v 505a51ff7d08, listing v3
   lib/A/Listing_prog.v 7ed1529926bd, listing-pins102 74dcda1eda12, as the cut carries them);
   every image value is read from a GENERATED name (A_prog_slot / A_entry_grow / A_prog_obj0 / A_prog_obj12), never
   typed. The image-generic facts are lib/A/Prog/PwGrowG.v (shared with image B's twin), the after-call step kit is
   lib/A/Prog/PRW_StepKit.v, the window call rule is the engine's YCbqGcallW.v, and the runners are
   YC80xf.v's _AJxf family (grow stores into the caller's struct, which preset keeps in a fake frame).
   Every conclusion is srealizes, through SRr' segs RZ_cf (YA0nH.v).
   Numerals: 80 is LENGTH (grow's own frame, = pi_frame F_grow); 56 / 48 / 40 / 32 / 24 / 8 / 4 are LENGTH (struct
   pj's field offsets and widths); 6 is a WORD (PJ_OBJ); 4096 and 2 ^ 47 are LENGTH (the allocator's lowest block and
   the stack bound of astk_ok). No address literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI00 YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK06 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC80xf YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YC80xf_inv.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG08cf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_StepKit PwGrowG PwGrowLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YGcfRehidePost YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
(* the A' instance of the Section's stand-ins (cited by qualified name at the end) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PALibA AD2l CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program listing's tree and word table as LITERALS (PAImg_prog.v's PL_prog_A has the same fields, with the
   tree as an unevaluated ptree_of_list): the engine's steps then never rebuild the 7000-slot tree *)
Definition grow_tpi : ptree asym := Eval vm_compute in ptree_of_list A_prog_listing.
Definition grow_tw : ctable := Eval vm_compute in tw_of 0 A_prog_listing.
Lemma grow_tpi_eq : ptree_of_list A_prog_listing = grow_tpi.
Proof. vm_cast_no_check (eq_refl grow_tpi). Qed.
Lemma grow_tw_eq : tw_of 0 A_prog_listing = grow_tw.
Proof. vm_cast_no_check (eq_refl grow_tw). Qed.
Lemma grow_lim : forallb (pinstr_atoms_ltb A_LIM) A_prog_listing = true.
Proof. vm_compute. reflexivity. Qed.
Lemma grow_len : 4 * Z.of_nat (length A_prog_listing) <= 2 ^ 40.
Proof. vm_compute. discriminate. Qed.
Definition PL_grow : PAListing A_prog_listing :=
  mkPAListing A_prog_listing grow_tpi grow_tpi_eq grow_tw grow_tw_eq grow_lim grow_len ltac:(vm_compute; exact I).

(* grow's entry, by name: its slot in the generated listing times the slot width *)
Definition GROW_OFF : Z := 4 * Z.of_nat (A_prog_slot AS_grow).

(* the symbolic entry state. Atoms: 0..31 the entry registers (sr_atoms), 32 the shadow base (the value of the image's
   shadow-base cell), 33..37 the node's type, kids, keys, n and cap. Regions: grow's own frame, the node's two halves
   (so that the n field, which grow does not write, is outside the written windows), the GOT word and the cell. *)
Definition grow_vA : YP09.region := YP09.mkRegion (Some 10%nat) 0 40 24 40
  [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition grow_vB : YP09.region := YP09.mkRegion (Some 10%nat) 40 56 48 56
  [YP09.mkChunk 40 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0))].
Definition grow_regions : smem := [stack_region 80; grow_vA; grow_vB; got_regionP; bcell_regionP 32].
Definition grow_Bx : sv := SOff 32 0.
Definition grow_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition grow_SH : list shent := [mkSHE 10 0 56].
Definition grow_extra (ty kids keys n cap : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 ty; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n; Z_to_bv 64 cap;
   Z_to_bv 64 (cap2R cap)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
(* LENGTH / DERIVED: the stack lies between 0x7fff7f800000 (DERIVED: asan_consts' lower bound of alloc_ceiling,
   which astk_ok puts below the stack; a CLOSED literal, so that vm_compute of the symbolic run never meets the
   Section's RunCeil variable) and 2 ^ 47; the node is below 2 ^ 47 and 8-aligned; the shadow base is SHADOW_OFF *)
Definition grow_facts : facts :=
  mkFacts [(2%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 56) 3);
           (32%nat, mkAF SHADOW_OFF SHADOW_OFF 3)] [] [].
Definition ss_grow0 : sstate := mkSS GROW_OFF sr_atoms grow_regions None grow_facts.
#[local] Existing Instance prh_img_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis TL : PALib (L := A_prog_listing) (PI := PI_prog_A) B.
(* the callee's text (the kit, lib/A/PRH_FnAlloc.v blob 4d8aeba047e5 at the cut): a STATED HYPOTHESIS until slice S1's walk of
   fuzz_realloc lands *)
Hypothesis HREALLOC : tfuzz_realloc_specX B ARx SK.

Definition RUN := @paj_run_xfR fx rc SK A_prog_listing PL_grow PI_prog_A B PST ARx cf_head LAWS (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Definition RET := @paj_ret_at fx rc A_prog_listing PL_grow PI_prog_A.
Definition BR := @paj_branchR fx rc A_prog_listing PI_prog_A (wle' SEGS RZ_cf).
(* the same runners carrying a memory invariant P (walk-S6's YC80xf_inv.v): the walk's P is the m-form keep
   `memnorm mem -> memnorm m`, kept ABSTRACT inside the walk and instantiated once at its top *)
Definition RUNP (P : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS P) :=
  @paj_run_xf_invR fx rc SK A_prog_listing PL_grow PI_prog_A B PST ARx cf_head LAWS P PLAW (wle' SEGS RZ_cf)
    (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).
Definition RUNTOP (P : (word -> option byte) -> Prop) (PLAW : srr_inv_laws SEGS P) :=
  @paj_run_to_xf_invR fx rc SK A_prog_listing PL_grow PI_prog_A B PST ARx cf_head LAWS P PLAW (wle' SEGS RZ_cf)
    (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf).

Lemma grow_ent : SIGMA AS_grow = BASE + GROW_OFF.
Proof. unfold GROW_OFF. vm_compute. reflexivity. Qed.

(* the written windows of grow's symbolic memory: its frame below sp, and the node's two written ranges (the GOT word
   and the shadow cell have an empty window) *)
Ltac grow_wr U2 U10 :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2, ?U10 in Hr; lia |]);
  contradiction.

Lemma grow_entry : forall ly S Hp (W : world SEGS) regs mem md ch v ty num str kids keys n cap,
  afn_pre_x SEGS B ARx (@STK_grow prh_img_A) ly S Hp W regs mem md ch ->
  getr regs 10 = w64 v -> v mod 8 = 0 -> 4096 <= v -> v + 56 <= 2 ^ 47 ->
  (v + 56 <= spZ regs - 80 \/ spZ regs <= v) ->
  (v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v) -> (v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v) ->
  (forall a, v <= a < v + 56 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) ->
  pj_hdrR SEGS (mrestrict (w_H W) mem) v ty num str kids keys n cap ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF v 56 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (grow_extra ty kids keys n cap))) ss_grow0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + GROW_OFF)) mem (seg_rom SEGS))) /\
  sh_ok SEGS grow_Bx grow_SH (Eimg (Ereg regs (grow_extra ty kids keys n cap))) (mrestrict (w_H W) mem).
Proof.
intros ly S Hp W regs mem md ch v ty num str kids keys n cap HPRE H10 Hv8 Hv4096 Hvhi Hvstk Hd0 Hd12 Happ HH HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 80 <= @STK_grow prh_img_A) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof HH as ((_ & HRW) & (Hty & Vty) & _ & _ & (Hkids & Vkids) & (Hkeys & Vkeys) & (Hn & Vn) & (Hcap & Vcap)).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 0 ltac:(lia)) as (O0lo & O0hi). pose proof (pa_obj_img 12 ltac:(lia)) as (O12lo & O12hi).
pose proof (pa_val_range (A_OBJ 0)) as R0. pose proof (pa_val_range (A_OBJ 12)) as R12.
cbn [pa_lo pa_hi PI_prog_A] in O0lo, O0hi, O12lo, O12hi.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
set (E := Eimg (Ereg regs (grow_extra ty kids keys n cap))).
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (grow_extra ty kids keys n cap) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 v).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10. }
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = v) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth grow_extra] in E32, E33, E34, E35, E36, E37.
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (EO0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EO12 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (UO0 : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0)) by (rewrite EO0; apply unsigned_lit_small; lia).
assert (UO12 : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12)) by (rewrite EO12; apply unsigned_lit_small; lia).
assert (DV : forall k w, ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> sv_denot E (SOff k 0) = Z_to_bv 64 w).
{ intros k w Hk Hw. cbn [sv_denot]. rewrite Hk, unsigned_lit_small by exact Hw. rewrite Z.add_0_r. reflexivity. }
rewrite restrict_mkst_fx. split.
- apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + unfold GROW_OFF. vm_compute. reflexivity.
  + unfold grow_regions. repeat apply Forall_cons; try apply Forall_nil.
    * unfold stack_region, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * unfold grow_vA, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ v 0 4 (SOff 33 0) ty); [apply DV; [exact E33 | lia] | exact Hty | lia |].
         rewrite Z.add_0_r. exact Vty.
      -- apply (chunk_ok_val SEGS E _ v 24 8 (SOff 34 0) kids); [apply DV; [exact E34 | lia] | exact Hkids | lia | exact Vkids].
      -- apply (chunk_ok_val SEGS E _ v 32 8 (SOff 35 0) keys); [apply DV; [exact E35 | lia] | exact Hkeys | lia | exact Vkeys].
    * unfold grow_vB, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ v 40 8 (SOff 36 0) n); [apply DV; [exact E36 | lia] | exact Hn | lia | exact Vn].
      -- apply (chunk_ok_val SEGS E _ v 48 8 (SOff 37 0) cap); [apply DV; [exact E37 | lia] | exact Hcap | lia | exact Vcap].
    * unfold got_regionP, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UO0.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
        [apply DV; [exact EO12 | lia] | change (8 * Z.of_N 8) with 64; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
    * unfold bcell_regionP, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UO12.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SHADOW_OFF);
        [apply DV; [exact E32 | unfold SHADOW_OFF; lia] | change (8 * Z.of_N 8) with 64; unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold grow_regions, stack_region, grow_vA, grow_vB, got_regionP, bcell_regionP.
    cbn [map zpairwise_disjoint zall_disjoint]. unfold extent_of_region, zdisj.
    cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite ?U2, ?U10, ?UO0, ?UO12. pose proof (pal_got_cell B TL) as Hgc. repeat split; lia.
  + unfold facts_ok, grow_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U10, U32.
    split; [split; [|split; [|split; [| exact I]]] | split; exact I].
    * split; [lia|]. split; [change (2 ^ 4) with 16; exact Hal16 | lia].
    * split; [lia|]. split; [change (2 ^ 3) with 8; exact Hv8 | lia].
    * split; [unfold SHADOW_OFF; lia|]. split; [vm_compute; reflexivity | lia].
- unfold sh_ok, grow_SH. apply Forall_cons; [|apply Forall_nil]. split.
  + unfold grow_Bx. cbn [she_m she_lo she_hi]. rewrite !U_SOff, U32, U10, !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; lia).
    change (rd_of SEGS (mrestrict (w_H W) mem)) with (aview SEGS (w_H W) mem). exact HRA.
  + unfold app_apart, grow_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
    rewrite !U_SOff, U32, U10, !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; lia).
    apply Happ. lia.
Qed.

(* the two image cells the walk reads - the GOT word of the shadow-base cell (A_OBJ 0) and the cell itself
   (A_OBJ 12) - lie in loaded segments of the image: the GOT word in the RELRO segment, the cell in the data
   segment (MEASURED on the pinned image with pyelftools: PT_LOAD 2 = [0xa19f0, 0xa3000), PT_LOAD 3 =
   [0xa3d20, 0x5ff7d0); the two values themselves come from A_prog_obj0 / A_prog_obj12, never typed here) *)
Lemma cell_img : forall c, c = VAL (A_OBJ 0) \/ c = VAL (A_OBJ 12) ->
  forall i, 0 <= i < 8 -> in_img SEGS (c + i).
Proof.
intros c Hc i Hi.
assert (Hv : c = 0xa2010 \/ c = 0xaaeb8)
  by (destruct Hc as [-> | ->]; [left | right]; vm_compute; reflexivity).
clear Hc. unfold in_img. destruct Hv as [-> | ->].
- eexists. split; [right; right; left; reflexivity|].
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
- eexists. split; [do 3 right; left; reflexivity|].
  match goal with |- Z.le ?lo _ /\ Z.lt _ (?lo' + ?sz) =>
    let l := eval vm_compute in lo in let h := eval vm_compute in sz in change lo with l; change sz with h end.
  lia.
Qed.




(* the program's PST (alloc.c's six statics and fuzz_preset.c's g_own_ran_out, PRH_Base ef7c8ca98529 prh_pst) are
   image bytes: PT_LOAD 3 of the pinned image (MEASURED with pyelftools on 1be0f53d / bff8519bbe3e, [0xa3d20, 0x5ff7d0))
   holds every one of prh_img_A's seven generated cells (PRH_Img 934516a622e8; #102 added g_most and g_own_ran_out) *)
Lemma pst_img : forall a, Exists (in_zr a) PST -> in_img SEGS a.
Proof.
intros a Ha. apply Exists_exists in Ha as ((lo & n) & Hin & Hr). unfold in_zr in Hr. cbn [fst snd] in Hr.
assert (Hb : 0xa3d20 <= lo /\ lo + n <= 0x5ff7d0).
{ unfold PST, prh_pst in Hin.
  change (pi_g_live, Z.of_nat pi_gz_live) with (0x5dd560, 8) in Hin.
  change (pi_g_peak, Z.of_nat pi_gz_peak) with (0x5dd580, 8) in Hin.
  change (pi_g_count, Z.of_nat pi_gz_count) with (0x5dd5a0, 8) in Hin.
  change (pi_g_fail, Z.of_nat pi_gz_fail) with (0xa65c0, 8) in Hin.
  change (pi_g_ran_out, Z.of_nat pi_gz_ran_out) with (0x5dd5c0, 1) in Hin.
  change (pi_g_most, Z.of_nat pi_gz_most) with (0xa65e0, 8) in Hin.
  change (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out) with (0x5dd540, 1) in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia |]); destruct Hin. }
unfold in_img. eexists. split; [do 3 right; left; reflexivity|].
match goal with |- Z.le ?lo0 _ /\ Z.lt _ (?lo' + ?sz) =>
  let l := eval vm_compute in lo0 in let h := eval vm_compute in sz in change lo0 with l; change sz with h end.
lia.
Qed.


(* ---- THE ENTRY DATA of one call of grow: one record, so the cut lemmas name the same entry state (S4's ps_in) ---- *)
Record gr_in : Type := mkGrIn {
  gi_ly : alayout; gi_S : astate; gi_Hp : list Z; gi_W : world SEGS;
  gi_regs : bvmap 5 word; gi_mem : word -> option byte; gi_md : Model; gi_ch : list (Z * Z * Z);
  gi_e : Z; gi_v : Z; gi_ty : Z; gi_num : Z; gi_str : Z; gi_kids : Z; gi_keys : Z; gi_n : Z; gi_cap : Z;
  gi_kb : list Z; gi_yb : list Z;
  gi_Lam : list (Z * Z); gi_peak : Z; gi_cnt : Z; gi_fail : Z; gi_ran : Z; gi_most : Z; gi_own : Z
}.
(* the entry environment of the walk: the registers, then the shadow base, the node's five fields and cap' *)
Definition gr_E (D : gr_in) : env :=
  Eimg (Ereg (gi_regs D) (grow_extra (gi_ty D) (gi_kids D) (gi_keys D) (gi_n D) (gi_cap D))).
(* the kit's footprint of grow (tgrow_specX's fpostWmR argument) *)
Definition gr_FP (D : gr_in) : list (Z * Z) :=
  [(gi_v D + 24, gi_v D + 40); (gi_v D + 48, gi_v D + 56)] ++
  ablocks_fp (prhReader_ab (kids_blkR (gi_kids D) (gi_cap D) ++ keys_blkR (gi_ty D) (gi_keys D) (gi_cap D))).

(* the two live counts of the text (position-free): the peak of each count along the ALL-GRANTED events *)
Definition gr_pk_sec (S : astate) (ty n cap : Z) : Prop :=
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV.
Definition gr_pk_24 (S : astate) (ty n cap : Z) : Prop :=
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (prhPg_evs (ty =? 6) n cap [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* tgrow_specX's premises (lib/A/PRH_FnReader.v blob f1ae32e3b2cd at the cut 7cdbb61b5fa0, :812-861: the
   post-implication form, the E sweep's ledger fields most / own, no run-word list DW, the live room at each event),
   at one record, in the text's order *)
Definition gr_pre (CTX0 : list (list Z)) (D : gr_in) : Prop :=
  fpre B ARx STK_grow (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_regs D) (gi_mem D) (gi_md D) (gi_ch D) /\
  prh_univ_closure B CTX0 /\
  (exists ch, achain (gi_ly D) (aview SEGS (w_H (gi_W D)) (gi_mem D)) (spZ (gi_regs D) - pi_frame F_grow)
     (prh_s0 F_grow (gi_v D)) ch) /\
  room_live_cf (gi_S D) /\
  gr_pk_sec (gi_S D) (gi_ty D) (gi_n D) (gi_cap D) /\
  gr_pk_24 (gi_S D) (gi_ty D) (gi_n D) (gi_cap D) /\
  PresetHullBudget.hull_budget (gi_S D) (prhPg_evs (gi_ty D =? 6) (gi_n D) (gi_cap D) []) /\
  getr (gi_regs D) 10 = w64 (gi_v D) /\ gi_v D <> 0 /\ gi_v D mod 8 = 0 /\
  pj_hdrR SEGS (mrestrict (w_H (gi_W D)) (gi_mem D)) (gi_v D) (gi_ty D) (gi_num D) (gi_str D) (gi_kids D) (gi_keys D)
    (gi_n D) (gi_cap D) /\
  pj_slots_atR (prh_lin (gi_Lam D)) (gi_ty D) (gi_kids D) (gi_keys D) (gi_n D) (gi_cap D) /\
  pj_apartR (kids_blkR (gi_kids D) (gi_cap D) ++ keys_blkR (gi_ty D) (gi_keys D) (gi_cap D)) (gi_v D) /\
  fwin (gi_ly D) (gi_W D) (gi_regs D) (gi_mem D) (gi_e D) /\
  prhReader_at B (gi_ly D) (gi_S D) (gi_Lam D) (gi_regs D) (gi_e D) (gi_v D) 56 /\
  range_addressable (aview SEGS (w_H (gi_W D)) (gi_mem D)) SHADOW_OFF (gi_v D) 56 /\
  (gi_n D = gi_cap D -> bytes_at (gi_W D) (gi_mem D) (gi_kids D) (gi_kb D) /\
     Z.of_nat (length (gi_kb D)) = 56 * gi_cap D /\
     (gi_ty D = 6 -> bytes_at (gi_W D) (gi_mem D) (gi_keys D) (gi_yb D) /\ Z.of_nat (length (gi_yb D)) = 8 * gi_cap D)) /\
  prh_ledger B (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_mem D) (gi_Lam D) (gi_peak D) (gi_cnt D) (gi_fail D) (gi_ran D)
    (gi_most D) (gi_own D) /\
  gi_cnt D + 2 < 2 ^ 64 - 1 /\
  (gi_n D = gi_cap D -> 56 * cap2R (gi_cap D) + cf_head < cf_malloc_max /\
     prh_live_evs (gi_S D) (prhPg_evs (gi_ty D =? 6) (gi_n D) (gi_cap D) [])).

(* tgrow_specX's post body: the kit's NAMED post tgrP_Q (lib/A/PRH_FnReader.v, the projection layer; its tgrP_Q_check fails
   to build if it ever differs from the text's post), over the entry values, so this walk's Q cannot drift from the text
   (near-copy row PwGrow.v:335, replaced by the alias); fpostWmR adds the memnorm keep *)
Definition gr_Q (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (v ty num str kids keys n cap : Z) (kb yb : list Z) (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tgrP_Q B most own ly S Hp W mem v ty num str kids keys n cap kb yb Lam peak cnt fail ran.
Definition gr_post (D : gr_in) : world SEGS -> config -> Prop :=
  fpostWmR B ARx SK (wle' SEGS RZ_cf) STK_grow (gi_e D) (gr_FP D) (gi_regs D) (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_mem D) (gi_md D)
    (gr_Q (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_mem D) (gi_v D) (gi_ty D) (gi_num D) (gi_str D) (gi_kids D)
       (gi_keys D) (gi_n D) (gi_cap D) (gi_kb D) (gi_yb D) (gi_Lam D) (gi_peak D) (gi_cnt D) (gi_fail D) (gi_ran D)
       (gi_most D) (gi_own D)).

(* ---- THE CALLEE. tfuzz_realloc_specX (PRH_FnAlloc.v blob 4d8aeba047e5 at the cut 7cdbb61b5fa0) is a LEAF in the post-implication form: no
   position at its entry; its post states, per outcome, the position step for ANY model run and position the caller
   picks (E = [] on a NULL, [HMal (n + cf_head)] at p = 0, [HRe (k + cf_head) (n + cf_head)] at p <> 0). So grow needs
   NO agreement between the model's grants and the instance's (AGREE-PREFIX, which the entry-keyed texts needed, is
   gone with them), and the live counts at each call come from the text's position-free pkR premises. ---- *)
(* fuzz_realloc's post body: the kit's NAMED post tfrP_Q (lib/A/PRH_FnAlloc.v, the projection layer; its tfrP_Q_check fails
   to build if it ever differs from tfuzz_realloc_specX's post), at a call from allocator state ly S Hp W with old block
   p (user size k, bytes old) and request n (near-copy row PwGrow.v:543, replaced by the alias) *)
Definition gr_KR (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (p k n : Z) (old : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tfrP_Q B ly S Hp W p k n old Lam peak cnt fail ran most own.
(* the kids realloc (A 0x86a68: a0 = kids, a1 = 56 cap') runs at the entry's allocator state (grow makes no allocator
   call before it); for cap = 0 its old block is NULL (pj_slots_atR) *)
Definition gr_KR_kids (D : gr_in) :=
  gr_KR (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_kids D) (56 * gi_cap D) (56 * cap2R (gi_cap D))
    (if gi_cap D =? 0 then [] else gi_kb D) (gi_Lam D) (gi_peak D) (gi_cnt D) (gi_fail D) (gi_ran D) (gi_most D) (gi_own D).

(* ---- THE JOIN (A 0x86a44): the two arms of `bnez s6` (cap' = 2 cap, cap' = 8) meet here. Both reach it with the
   same symbolic state except s6 (SAlu ALU_SLL (SOff 37 0) (SLit 1) / SLit 8) and the branch fact; s6 is re-pinned to
   atom 38 (= cap2R cap, grow_extra) and the branch fact dropped, so ONE state continues (MEASURED: both arms' states
   printed by the build, the internal file build-20261029T090307Z.log) ---- *)
Definition grow_frame : YP09.region := YP09.mkRegion (Some 2%nat) (-80) 0 (-80) 0
  [YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
   YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
   YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
   YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
   YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition ss_grow_J : sstate :=
  mkSS (GROW_OFF + 136)
    [SLit 0; SOff 1 0; SOff 2 (-80); SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 10 48; SOff 10 0;
     SOff 36 0; SLit 0; SOff 12 0; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0; SOff 18 0; SOff 19 0;
     SOff 20 0; SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 48) (SLit 3)) (SOff 32 0); SOff 38 0; SOff 32 0;
     SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0]
    [grow_frame; grow_vA; grow_vB; got_regionP; bcell_regionP 32]
    None
    (mkFacts (f_atoms grow_facts) [mkAC BC_GEU (SOff 36 0) (SOff 37 0)] []).

(* a register's term replaced by another of the same value *)
Lemma st_ok_pi_pin : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss ms -> sv_denot E e = sv_denot E (sr_get (ss_regs ss) r) ->
  st_ok_pi SEGS VAL E (mkSST (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS He. unfold st_ok_pi in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (H7' : regs_ok E (ss_regs ss) (ms_regs ms)) by exact H7.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [|split; [exact H8 | exact H9]].
change (regs_ok E (sr_set (ss_regs ss) r e) (ms_regs ms)).
intros r'. rewrite (H7' r'). unfold YP0l.sr_get, YP0l.sr_set.
destruct (bv_eqb r' (0%bv : bv 5)) eqn:HR0; [reflexivity|].
destruct (bv_eqb r (0%bv : bv 5)) eqn:Hr0; [reflexivity|].
rewrite YP0l.nth_sr_upd. destruct (Nat.eqb (YP0l.ridx r') (YP0l.ridx r)) eqn:Hi; [|reflexivity].
apply Nat.eqb_eq in Hi. apply YP0l.ridx_inj in Hi. subst r'. unfold YP0l.sr_get in He. rewrite Hr0 in He.
symmetry. exact He.
Qed.

(* a branch fact dropped *)
Lemma st_ok_pi_drop_cond : forall E pc regs fregs mem resv A c C AL ms,
  st_ok_pi SEGS VAL E (mkSST pc regs fregs mem resv (mkFacts A (c :: C) AL)) ms ->
  st_ok_pi SEGS VAL E (mkSST pc regs fregs mem resv (mkFacts A C AL)) ms.
Proof.
intros E pc regs fregs mem resv A c C AL ms HS. unfold st_ok_pi in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|].
assert (H9' : facts_ok E (mkFacts A (c :: C) AL)) by exact H9.
change (facts_ok E (mkFacts A C AL)).
destruct H9' as (HA & HC & HL). split; [exact HA|]. split; [exact (proj2 HC) | exact HL].
Qed.


(* the read-only view survives grow's own stores: they are in its frame (above alloc_ceiling) or in the node (off the
   image), and every read-only byte is an image byte *)
Lemma grow_ro_keep : forall (W : world SEGS) mem m' sp v,
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A) (@pa_relro_hi _ A_prog_listing PI_prog_A) B (aview SEGS (w_H W) mem) ->
  (forall x : word, ~ grow_wr 80 sp v (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) mem x) ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) -> YM05.alloc_ceiling <= sp - 80 ->
  arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A) (@pa_relro_hi _ A_prog_listing PI_prog_A) B (aview SEGS (w_H W) m').
Proof.
intros W mem m' sp v HRO HF Hoff Hsp a Hro Hown Herr.
assert (Himg : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)]).
pose proof (pa_segs_low a Himg) as Hlow. pose proof asan_consts as (C1 & _). unfold kLowMemEnd in Hlow.
rewrite <- (HRO a Hro Hown Herr). apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
unfold grow_wr. intros [Hw | [Hw | Hw]]; [lia | exact (Hoff a ltac:(lia) Himg) | exact (Hoff a ltac:(lia) Himg)].
Qed.

(* a byte array outside grow's windows survives its stores *)
Lemma grow_bytes_keep : forall (W : world SEGS) mem m' sp v p l,
  bytes_at W mem p l ->
  (forall x : word, ~ grow_wr 80 sp v (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) mem x) ->
  0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ grow_wr 80 sp v a) ->
  bytes_at W m' p l.
Proof.
intros W mem m' sp v p l HB HF Hp0 Hp64 Hnw. unfold bytes_at in *. apply (garr8_frame SEGS _ _ p l HB).
intros a Ha. unfold mbyte. rewrite HF; [reflexivity|]. rewrite unsigned_lit_small by lia. exact (Hnw a Ha).
Qed.


(* a stretch whose symbolic memory writes only grow's frame (after a re-seat that dropped the node's regions) *)
Lemma grow_awr_ok_stk : forall E rs STK FR e sp FP bl0 blc S ly,
  0 <= FR -> FR <= STK -> 0 <= e ->
  (forall a, in_wrange E rs a -> sp - FR <= a < sp) ->
  awr_ok_fr E rs (STK + e) (sp + e) FP bl0 blc S ly [].
Proof. intros E rs STK FR e sp FP bl0 blc S ly HFR0 HFR He Hw a Ha. left. left. specialize (Hw a Ha). lia. Qed.
Ltac grow_wr_stk Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; lia |]);
  contradiction.


(* the node's header moves with its 56 bytes: equal views and present bytes at the new memory (any world) *)
Lemma pj_hdr_aview : forall (H H' : word -> bool) (m m' : word -> option byte) v ty num str kids keys n cap,
  pj_hdrR SEGS (mrestrict H m) v ty num str kids keys n cap ->
  (forall a, v <= a < v + 56 -> aview SEGS H' m' a = aview SEGS H m a /\ apresent H' m' a) ->
  pj_hdrR SEGS (mrestrict H' m') v ty num str kids keys n cap.
Proof.
intros H H' m m' v ty num str kids keys n cap
  ((Hv8 & HRW) & (Hty & Vty) & (Hnum & Vnum) & (Hstr & Vstr) & (Hk & Vk) & (Hy & Vy) & (Hn & Vn) & (Hc & Vc)) HE.
assert (VM : forall a (nb : nat) w, v <= a -> a + Z.of_nat nb <= v + 56 ->
  val_mem SEGS (mrestrict H m) a nb w -> val_mem SEGS (mrestrict H' m') a nb w).
{ intros a nb w Ha Hb Hw kk Hkk. destruct (HE (a + Z.of_nat kk)) as [E1 _]; [lia|].
  rewrite (mbyte_of_aview SEGS H H' m m' _ E1). exact (Hw kk Hkk). }
split; [split; [exact Hv8 | intros x Hx; apply (apresent_writable SEGS); exact (proj2 (HE x Hx))]|].
split; [split; [exact Hty | apply (VM v 4%nat ty); [lia | cbn; lia | exact Vty]]|].
split; [split; [exact Hnum | apply (VM (v + 8) 8%nat num); [lia | cbn; lia | exact Vnum]]|].
split; [split; [exact Hstr | apply (VM (v + 16) 8%nat str); [lia | cbn; lia | exact Vstr]]|].
split; [split; [exact Hk | apply (VM (v + 24) 8%nat kids); [lia | cbn; lia | exact Vk]]|].
split; [split; [exact Hy | apply (VM (v + 32) 8%nat keys); [lia | cbn; lia | exact Vy]]|].
split; [split; [exact Hn | apply (VM (v + 40) 8%nat n); [lia | cbn; lia | exact Vn]]|].
split; [exact Hc | apply (VM (v + 48) 8%nat cap); [lia | cbn; lia | exact Vc]].
Qed.

(* a byte array moves with equal views (any world) *)
Lemma bytes_at_aview : forall (W W' : world SEGS) m m' p l,
  bytes_at W m p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  bytes_at W' m' p l.
Proof.
intros W W' m m' p l HB HE j Hj. destruct (HB j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (p + Z.of_nat j + Z.of_nat k)); [exact (Hv k Hk)|].
apply HE. lia.
Qed.

Lemma rd32_aview : forall (rd rd' : reader) a w,
  rd32 rd a w -> (forall x, a <= x < a + 4 -> rd' x = rd x) -> rd32 rd' a w.
Proof. intros rd rd' a w H HE k Hk. rewrite HE by lia. exact (H k Hk). Qed.

(* what grow's granted trace charges at n = cap: the kids realloc, and the keys realloc for an object *)
Lemma grow_held_nat : forall (o : bool) (c : nat),
  PjGrammar.held (snd (fst (PjGrammar.grow o c c []))) +
    cf_head * Z.of_nat (PjGrammar.calls (snd (fst (PjGrammar.grow o c c [])))) =
  Z.of_nat (56 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (56 * c)%nat + cf_head +
  (if o then Z.of_nat (8 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (8 * c)%nat + cf_head else 0).
Proof.
intros o c. unfold PjGrammar.grow. rewrite Nat.ltb_irrefl. cbv zeta.
generalize (if Nat.eqb c 0 then 8%nat else (2 * c)%nat) as c'. intros c'.
destruct o; cbn [PjGrammar.jbind PjGrammar.jrealloc PjGrammar.take PjGrammar.jret fst snd app
  PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia.
Qed.
Lemma grow_held_eq : forall (o : bool) cap, 0 <= cap ->
  PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace o cap cap) =
  56 * (cap2R cap - cap) + cf_head + (if o then 8 * (cap2R cap - cap) + cf_head else 0).
Proof.
intros o cap Hc. unfold PRH_Charge.prh_held, PRH_Charge.prhPg_gtrace. rewrite grow_held_nat. unfold cap2R.
destruct (Z.eqb_spec cap 0) as [H0 | H0].
- subst cap. change (Z.to_nat 0) with 0%nat. cbn [Nat.eqb]. destruct o; lia.
- rewrite (proj2 (Nat.eqb_neq (Z.to_nat cap) 0)) by lia. destruct o; lia.
Qed.

(* ---- the facts the kids-moved arms add: the ledger sum, the granted trace's net bytes, a repeated block, a hidden
   head set, a byte prefix, the node apart from a new block, and the shadow facts across grow's own stores ---- *)
Lemma grow_lsum_app : forall l1 l2, Ledger.lsum (l1 ++ l2) = Ledger.lsum l1 + Ledger.lsum l2.
Proof. induction l1 as [|[a k] l1 IH]; intros l2; cbn [app Ledger.lsum]; [lia | rewrite IH; lia]. Qed.
Lemma grow_lsum_perm : forall l l', Permutation l l' -> Ledger.lsum l = Ledger.lsum l'.
Proof.
intros l l' H. induction H as [|[a k] l l' H IH|[a k] [a' k'] l|l l' l'' H1 IH1 H2 IH2]; cbn [Ledger.lsum]; lia.
Qed.
Lemma grow_lsum_kids : forall kids cap, 0 <= cap -> Ledger.lsum (kids_blkR kids cap) = 56 * cap.
Proof. intros kids cap H. unfold kids_blkR. destruct (Z.eqb_spec cap 0); cbn [Ledger.lsum]; lia. Qed.
Lemma grow_lsum_keys : forall ty keys cap, 0 <= cap -> ty = 6 -> Ledger.lsum (keys_blkR ty keys cap) = 8 * cap.
Proof.
intros ty keys cap H H6. unfold keys_blkR. rewrite (proj2 (Z.eqb_eq ty 6) H6).
destruct (Z.eqb_spec cap 0); cbn [orb negb Ledger.lsum]; lia.
Qed.

(* the net user bytes of grow's granted trace at n = cap (grow_held_nat without the heads) *)
Lemma grow_held_nat2 : forall (o : bool) (c : nat),
  PjGrammar.held (snd (fst (PjGrammar.grow o c c []))) =
  Z.of_nat (56 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (56 * c)%nat +
  (if o then Z.of_nat (8 * (if Nat.eqb c 0 then 8 else 2 * c))%nat - Z.of_nat (8 * c)%nat else 0).
Proof.
intros o c. unfold PjGrammar.grow. rewrite Nat.ltb_irrefl. cbv zeta.
generalize (if Nat.eqb c 0 then 8%nat else (2 * c)%nat) as c'. intros c'.
destruct o; cbn [PjGrammar.jbind PjGrammar.jrealloc PjGrammar.take PjGrammar.jret fst snd app
  PjGrammar.held PjGrammar.held_ev]; lia.
Qed.
Lemma grow_held_only : forall (o : bool) cap, 0 <= cap ->
  PjGrammar.held (PRH_Charge.prhPg_gtrace o cap cap) =
  56 * (cap2R cap - cap) + (if o then 8 * (cap2R cap - cap) else 0).
Proof.
intros o cap Hc. unfold PRH_Charge.prhPg_gtrace. rewrite grow_held_nat2. unfold cap2R.
destruct (Z.eqb_spec cap 0) as [H0 | H0].
- subst cap. change (Z.to_nat 0) with 0%nat. cbn [Nat.eqb]. destruct o; lia.
- rewrite (proj2 (Nat.eqb_neq (Z.to_nat cap) 0)) by lia. destruct o; lia.
Qed.

(* an element repeated in a pairwise list is related to itself *)
Lemma pairwise_dup {X} : forall (R : X -> X -> Prop) (l r : list X) y,
  pairwise R (l ++ y :: r) -> In y l -> R y y.
Proof.
intros R l. induction l as [|z l IH]; intros r y P Hin; [destruct Hin|].
cbn in P. destruct P as [F P]. destruct Hin as [Hzy | Hin].
- subst z. rewrite Forall_forall in F. apply F. apply in_or_app. right. left. reflexivity.
- exact (IH r y P Hin).
Qed.

(* THE NEW BLOCK OF A MALLOC IS NOT ALREADY LIVE: prh_alloc_post's append equality (PRH_FnAlloc.v:234) and the post
   state's pairwise disjointness (ARx_sep_law): a repeated block would be disjoint from itself, and its request size
   is positive. (* REPLACE by the kit's lemma when it lands *) *)
Lemma grow_alloc_fresh : forall ly S ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 b m,
  ARx ly2 S2 Hp2 W2 mem2 md2 -> 0 <= m -> ablocks B ly2 S2 = ablocks B ly S ++ [(b, m)] ->
  ~ In (b, m) (ablocks B ly S).
Proof.
intros ly S ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hm0 Eab Hin.
destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Hpw & _).
rewrite Eab, map_app, <- app_assoc in Hpw. cbn [map app fst snd] in Hpw.
apply (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0)))) in Hin.
pose proof (pairwise_dup zdisjoint _ _ _ Hpw Hin) as Hd.
assert (Hq : 1 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* perm_remove_nodup, ledger_hp_nodup and bytes_at_prefix are PwGrowG.v's (one home for A' and B', blob 74c168992b48) *)

Lemma ew_havoc_hi : forall E k ws i, (k + length ws <= i)%nat -> ew (havoc E k ws) i = ew E i.
Proof.
intros E k ws i Hi. unfold havoc. cbn [ew]. destruct (i <? k)%nat eqn:Hlt; [reflexivity|].
apply nth_overflow. lia.
Qed.

(* THE NODE IS APART FROM THE NEW BLOCK a successful fuzz_realloc returns (its SUCCESS arm's pieces, as grow_at_kept
   takes them): a block holding the node at the call state survives the call and is not the new block, so the post
   state's disjointness separates them; a fake frame by the block-frame law; the caller's extension is above every
   block *)
Lemma grow_new_apart : forall ly S Hp (W : world SEGS) mem md ly2 S2 Hp2 (W2 : world SEGS) mem2 md2
  Lam regs e v p k nn res b1 b2,
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall a kk, In (a, kk) Lam -> In (a - cf_head, kk + cf_head) (ablocks B ly S)) ->
  prhReader_at B ly S Lam regs e v 56 ->
  (forall x, pj_holdsR (p, k) x -> ~ (v <= x < v + 56)) -> In (p, k) Lam ->
  ablocks B ly S = b1 ++ (p - cf_head, k + cf_head) :: b2 ->
  Permutation (ablocks B ly2 S2) ((res - cf_head, nn + cf_head) :: b1 ++ b2) ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  ~ In (res - cf_head, nn + cf_head) (b1 ++ b2) -> YM05.alloc_ceiling <= spZ regs ->
  forall x, res - cf_head <= x < res - cf_head + req_size (nn + cf_head) -> ~ (v <= x < v + 56).
Proof.
intros ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v p k nn res b1 b2
  HAR HAR2 HLAM HAt HAPp Hpk Eab Hperm Hfrs Hfa Hfresh Hsp x Hx Hxv.
pose proof cf_head_nonneg as Hh0.
assert (Hnew2 : In (res - cf_head, nn + cf_head) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnew2) as (_ & _ & Hnc & _).
assert (HKEEP : forall b m, In (b, m) (ablocks B ly S) -> (b, m) <> (p - cf_head, k + cf_head) ->
  b <= v -> v + 56 <= b + req_size m -> False).
{ intros b m Hin Hne Hb1 Hb2.
  assert (Hin12 : In (b, m) (b1 ++ b2)).
  { rewrite Eab in Hin. apply in_app_or in Hin as [Hb | [Hq | Hb]];
      [apply in_or_app; left; exact Hb | exfalso; apply Hne; rewrite <- Hq; reflexivity
       | apply in_or_app; right; exact Hb]. }
  assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hin12).
  assert (Hne2 : (b, m) <> (res - cf_head, nn + cf_head)) by (intros Hq; apply Hfresh; rewrite <- Hq; exact Hin12).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hin2 Hnew2 Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HKEEP (a' - cf_head) (k' + cf_head) (HLAM _ _ Hin')); [| lia | lia].
  intros Hq. injection Hq as E1 E2.
  apply (HAPp v); [unfold pj_holdsR; cbn [fst snd]; lia | lia].
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HKEEP b m Hinb); [| lia | lia].
  intros Hq. injection Hq as E1 E2. apply Hnot.
  replace (b + cf_head) with p by lia. replace (m - cf_head) with k by lia. exact Hpk.
- rewrite <- Hfrs in Hinf.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hnew2 Hinf) as Hd.
  rewrite Hfa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* the same for the MALLOC shape (prh_alloc_post's SUCCESS arm: the new block appended) *)
Lemma grow_new_apart0 : forall ly S Hp (W : world SEGS) mem md ly2 S2 Hp2 (W2 : world SEGS) mem2 md2
  Lam regs e v nn res,
  ARx ly S Hp W mem md -> ARx ly2 S2 Hp2 W2 mem2 md2 ->
  (forall a kk, In (a, kk) Lam -> In (a - cf_head, kk + cf_head) (ablocks B ly S)) ->
  prhReader_at B ly S Lam regs e v 56 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, nn + cf_head)] ->
  frames S2 = frames S -> (forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos) ->
  YM05.alloc_ceiling <= spZ regs -> 0 <= nn ->
  forall x, res - cf_head <= x < res - cf_head + req_size (nn + cf_head) -> ~ (v <= x < v + 56).
Proof.
intros ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v nn res HAR HAR2 HLAM HAt Eab Hfrs Hfa Hsp Hnn x Hx Hxv.
pose proof cf_head_nonneg as Hh0.
assert (Hm0 : 0 <= nn + cf_head) by lia.
pose proof (grow_alloc_fresh ly S ly2 S2 Hp2 W2 mem2 md2 (res - cf_head) (nn + cf_head) HAR2 Hm0 Eab) as Hfresh.
assert (Hnew2 : In (res - cf_head, nn + cf_head) (ablocks B ly2 S2))
  by (rewrite Eab; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnew2) as (_ & _ & Hnc & _).
assert (HKEEP : forall b m, In (b, m) (ablocks B ly S) -> b <= v -> v + 56 <= b + req_size m -> False).
{ intros b m Hin Hb1 Hb2.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Eab; apply in_or_app; left; exact Hin).
  assert (Hne2 : (b, m) <> (res - cf_head, nn + cf_head)) by (intros Hq; apply Hfresh; rewrite <- Hq; exact Hin).
  pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hin2 Hnew2 Hne2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & Hnot & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HKEEP _ _ (HLAM _ _ Hin')); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HKEEP b m Hinb); lia.
- rewrite <- Hfrs in Hinf.
  pose proof (sep_block_frame_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ cid pos HAR2 Hnew2 Hinf) as Hd.
  rewrite Hfa in Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- lia.
Qed.

(* two successive swaps compose: the second's old blocks lie in the first's rest (the first's new block is not
   among them) *)
Lemma perm_swap2 {T} : forall (A X Y D1 D2 : list T) (N1 : T),
  Permutation A (D1 ++ X) -> Permutation (N1 :: X) (D2 ++ Y) -> ~ In N1 D2 ->
  exists Z0, Permutation A ((D1 ++ D2) ++ Z0) /\ Permutation Y (N1 :: Z0).
Proof.
intros A X Y D1 D2 N1 HA HX Hn.
assert (HinY : In N1 Y).
{ pose proof (Permutation_in N1 HX (or_introl eq_refl)) as Hi. apply in_app_or in Hi as [Hi | Hi];
    [contradiction | exact Hi]. }
destruct (in_split _ _ HinY) as (y1 & y2 & Ey). exists (y1 ++ y2). split.
- eapply perm_trans; [exact HA|]. rewrite <- app_assoc. apply Permutation_app_head.
  apply (Permutation_cons_inv (a := N1)). eapply perm_trans; [exact HX|]. rewrite Ey, !app_assoc.
  apply Permutation_sym. apply Permutation_middle.
- rewrite Ey. apply Permutation_sym. apply Permutation_middle.
Qed.

(* a read-only byte of the image is not an alloc.c static: the statics are in PT_LOAD 3 [0xa3d20, 0x5ff7d0)
   (pst_img's measurement), every read-only segment and the RELRO range lie below it *)
Lemma ro_not_pst : forall a, in_roP SEGS (@pa_relro_lo _ A_prog_listing PI_prog_A) (@pa_relro_hi _ A_prog_listing PI_prog_A) a -> ~ Exists (in_zr a) PST.
Proof.
intros a Hro Hp.
assert (Hb : 0xa3d20 <= a).
{ apply Exists_exists in Hp as ((lo & n) & Hin & Hr). unfold in_zr in Hr. cbn [fst snd] in Hr.
  unfold PST, prh_pst in Hin.
  change (pi_g_live, Z.of_nat pi_gz_live) with (0x5dd560, 8) in Hin.
  change (pi_g_peak, Z.of_nat pi_gz_peak) with (0x5dd580, 8) in Hin.
  change (pi_g_count, Z.of_nat pi_gz_count) with (0x5dd5a0, 8) in Hin.
  change (pi_g_fail, Z.of_nat pi_gz_fail) with (0xa65c0, 8) in Hin.
  change (pi_g_ran_out, Z.of_nat pi_gz_ran_out) with (0x5dd5c0, 1) in Hin.
  change (pi_g_most, Z.of_nat pi_gz_most) with (0xa65e0, 8) in Hin.
  change (pi_g_own_ran_out, Z.of_nat pi_gz_own_ran_out) with (0x5dd540, 1) in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia |]); destruct Hin. }
destruct Hro as [(s & Hs & Hw & Hr) | Hr].
- assert (H : In (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)
                 (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) SEGS))
    by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) SEGS s Hs).
  rewrite Hw in H. remember (Z.of_N (seg_base s)) as b eqn:Eb. remember (Z.of_N (seg_size s)) as z eqn:Ez.
  clear Eb Ez. vm_compute in H.
  repeat (destruct H as [H | H]; [inversion H; subst; lia |]). destruct H.
- cbn [pa_relro_lo pa_relro_hi PI_prog_A] in Hr. unfold A_prog_relro_lo, A_prog_relro_hi in Hr. lia.
Qed.

(* the node's place survives a step that keeps the blocks, the frames and their addresses *)
Lemma prhReader_at_eq : forall ly S Lam ly' S' regs e v n,
  ablocks B ly' S' = ablocks B ly S -> frames S' = frames S ->
  (forall cid pos, frame_addr ly' cid pos = frame_addr ly cid pos) ->
  prhReader_at B ly S Lam regs e v n -> prhReader_at B ly' S' Lam regs e v n.
Proof.
intros ly S Lam ly' S' regs e v n Eab Efr Efa H. unfold prhReader_at in *. rewrite Eab, Efr.
destruct H as [H | [H | [(cid & pos & Hin & H1 & H2) | H]]];
  [left; exact H | right; left; exact H | right; right; left; exists cid, pos; rewrite !Efa; exact (conj Hin (conj H1 H2))
  | right; right; right; exact H].
Qed.

(* a live harness block (its head hidden) has the shadow facts of a new block: AR_laws_x field 14 *)
Lemma hblock_vis : forall ly S Hp (W : world SEGS) mem md a k,
  ARx ly S Hp W mem md -> In (a - cf_head, k + cf_head) (ablocks B ly S) -> In (a - cf_head) Hp ->
  a mod 8 = 0 -> k mod 8 = 0 -> 0 < k -> prhReader_vis W mem a k.
Proof.
intros ly S Hp W mem md a k HAR Hin Hhp Ha8 Hk8 Hk0.
pose proof cf_head_nonneg as Hh0.
destruct (alx_hshadow _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hin Hhp) as (Hbs & Hhv).
assert (Erq : req_size (k + cf_head) = k + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
rewrite Erq in Hbs, Hhv. replace (a - cf_head + cf_head) with a in Hbs, Hhv by lia.
replace (k + cf_head - cf_head) with k in Hbs, Hhv by lia.
split; [| intros _; apply Hhv; lia].
destruct Hbs as (_ & _ & Hbs). intros x Hx.
assert (Hq : 0 <= (x - a) / 8 < k / 8 /\ k / 8 <= (k + 7) / 8 /\
             shadow_of_addr SHADOW_OFF x = shadow_of_addr SHADOW_OFF a + (x - a) / 8).
{ unfold shadow_of_addr. Z.div_mod_to_equations. lia. }
destruct Hq as (Hi1 & Hi2 & Esh). exists 0. split; [|left; reflexivity].
assert (Hi3 : 0 <= (x - a) / 8 < (k + 7) / 8) by lia.
rewrite Esh, (Hbs ((x - a) / 8) Hi3). rewrite (proj2 (Z.ltb_lt _ _) (proj2 Hi1)). reflexivity.
Qed.

(* grow_v_kept with the footprint's apartness from the node as the premise: the keys call's footprint is the keys
   block, apart from the node by the entry's slot facts, while the harness list at that call no longer holds the
   entry's kids block *)
Lemma grow_v_kept_nf : forall ly S Hp (W : world SEGS) memc mdc Lam peak cnt fail ran most own regs e v
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ARx ly S Hp W memc mdc -> prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 -> YM05.alloc_ceiling + 128 <= spZ regs -> 4096 <= v -> v + 56 <= 2 ^ 64 ->
  (forall a, v <= a < v + 56 -> ~ in_img SEGS a) ->
  (forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W) memc a) ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  sp1 <= spZ regs ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  forall a, v <= a < v + 56 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a /\ apresent (w_H W2) mem2 a.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1
  HAR HL HAt Hsp Hv0 Hv64 Hoff Hpc HJ Hsp1 HnF0 a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & _ & G4 & Hgone & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as Hh0.
pose proof (HnF0 a Ha) as HnF.
assert (HTR : aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a -> apresent (w_H W) memc a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros Hv Hpm. split; [exact Hv|]. eapply apresent_transfer; [lia | exact (Hoff a Ha) | exact Hv | exact Hpm]. }
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a /\ apresent (w_H W2) mem2 a).
{ intros p m Hin Hpv1 Hpv2.
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & Hpr & _).
  apply HTR; [| exact (proj1 (Hpr a ltac:(lia)))].
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - replace a with (p + (a - p)) by lia.
    apply (G2 p m (a - p) Hin Hin2); [lia |]. replace (p + (a - p)) with a by lia. exact HnF.
  - exfalso. apply HnF. replace a with (p + (a - p)) by lia. exact (Hgone p m (a - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK _ _ Hinb); lia.
- destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ cid pos HAR Hinf) as (_ & _ & Hfp & _).
  apply HTR; [| exact (proj1 (Hfp a ltac:(lia)))].
  apply (G4 cid pos a Hinf); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact HnF].
- apply HTR; [apply G1; lia | apply Hpc; lia].
Qed.

(* grow_vloc2 with the same premise *)
Lemma grow_vloc2_nf : forall ly S Hp (W : world SEGS) memc mdc Lam peak cnt fail ran most own regs e v
  STK1 sp1 FP1 ly2 S2 Hp2 (W2 : world SEGS) mem2 md2 k1,
  ARx ly S Hp W memc mdc -> prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs e v 56 ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) STK1 sp1 FP1 ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall x, v <= x < v + 56 -> ~ inFP FP1 x) ->
  grow_vloc B ly2 S2 regs e v.
Proof.
intros ly S Hp W memc mdc Lam peak cnt fail ran most own regs e v STK1 sp1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 HAR HL HAt HJ HnFv.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & Hgone & _).
pose proof cf_head_nonneg as Hh0.
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
assert (HBLK2 : forall p m, In (p, m) (ablocks B ly S) -> p <= v -> v + 56 <= p + req_size m ->
  grow_vloc B ly2 S2 regs e v).
{ intros p m Hin Hpv1 Hpv2.
  destruct (in_dec Hdec (p, m) (ablocks B ly2 S2)) as [Hin2 | Hout].
  - left. exists p, m. split; [exact Hin2 | lia].
  - exfalso. apply (HnFv v ltac:(lia)). replace v with (p + (v - p)) by lia.
    exact (Hgone p m (v - p) Hin Hout ltac:(lia)). }
destruct HAt as [(a' & k' & Hin' & H1 & H2) | [(b & m & Hinb & _ & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | (H1 & H2)]]].
- pose proof HL as (_ & _ & HF & _).
  pose proof (proj1 (Forall_forall _ _) HF (a', k') Hin') as (Hk' & Hb' & _). cbn [fst snd] in Hk', Hb'.
  assert (Hq' : k' + cf_head <= req_size (k' + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k' + cf_head) 0); lia).
  apply (HBLK2 _ _ Hb'); lia.
- assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  apply (HBLK2 _ _ Hinb); lia.
- right; left. exists cid, pos. unfold frame_addr in *.
  destruct Hly as (_ & _ & _ & _ & _ & HlyF & _). rewrite HlyF, Hfrs. cbn [app].
  split; [exact Hinf | lia].
- right; right. lia.
Qed.

(* a new block's shadow facts survive a change that leaves the shadow band alone *)
Lemma vis_keep : forall (rd rd' : reader) a n,
  (forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 - 64 ->
  range_addressable rd SHADOW_OFF a n -> (0 < n -> shadow_hull_vis rd a n) ->
  range_addressable rd' SHADOW_OFF a n /\ (0 < n -> shadow_hull_vis rd' a n).
Proof.
intros rd rd' a n Hag Ha0 Han HRA HV. split.
- intros x Hx. destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite Hag; [exact Hs|]. unfold SHADOW_OFF in *. Z.div_mod_to_equations. lia.
- intros Hn s Hs. rewrite Hag; [exact (HV Hn s Hs)|]. unfold shadow_addr, SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

(* lia without the universally quantified hypotheses (the tuned lia instantiates them, which explodes in the
   walk's large contexts) *)
(* lia without the disjunctive hypotheses (a refutation that needs one splits on all of them) *)
Ltac dlia := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.
Ltac flia := repeat match goal with
  | H : forall _ : Z, _ |- _ => clear H
  | H : forall _ : word, _ |- _ => clear H
  | H : forall _ : nat, _ |- _ => clear H
  end; lia.

(* fpre's `raZ regs < YM05.alloc_ceiling` at grow's two call sites: the return pc is a slot of the listing, so it is
   an image byte, so below kLowMemEnd <= YM05.alloc_ceiling (PRW_StepKit.pa_slot_lt_ceil_b, the one copy). ONE CLOSED
   TOP-LEVEL LEMMA PER SLOT: with the listing instance implicit the evar sits under vm_compute and the goal runs away
   (measured). *)
Lemma grow_kids_ret_ceil : BASE + (GROW_OFF + 176) < YM05.alloc_ceiling.
Proof.
apply (pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_grow) (PI := PI_prog_A) (GROW_OFF + 176));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.
Lemma grow_keys_ret_ceil : BASE + (GROW_OFF + 256) < YM05.alloc_ceiling.
Proof.
apply (pa_slot_lt_ceil_b (L := A_prog_listing) (PL := PL_grow) (PI := PI_prog_A) (GROW_OFF + 256));
  [split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | vm_compute; reflexivity].
Qed.

(* THE WALK FROM THE JOIN: the kids call, its four arms, the keys call and its three, and the returns *)
Lemma grow_from_J : forall CTX0 (D : gr_in) ms mdg (P : (word -> option byte) -> Prop),
  srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  (forall m, P m -> YAkMemnorm.memnorm SEGS (gi_mem D) -> YAkMemnorm.memnorm SEGS m) ->
  gr_pre CTX0 D -> gi_n D = gi_cap D -> P (ms_mem ms) ->
  st_ok_pi SEGS VAL (gr_E D) ss_grow_J (restrict (w_H (gi_W D)) ms) ->
  sh_ok SEGS grow_Bx grow_SH (gr_E D) (mrestrict (w_H (gi_W D)) (ms_mem ms)) ->
  ajournal_xR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (STK_grow + gi_e D) (spZ (gi_regs D) + gi_e D) (gr_FP D)
    (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (gi_mem D) (gi_md D) []
    (gi_ly D) (gi_S D) (gi_Hp D) (gi_W D) (ms_mem ms) mdg 0 ->
  cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) STK_grow (spZ (gi_regs D)) (grow_OR (gi_v D)) (gr_FP D)
    (gi_ly D) (gi_S D) (gi_W D) (gi_mem D) (gi_md D) (gi_ly D) (gi_S D) (gi_W D) (ms_mem ms) mdg ->
  (forall x : word, ~ grow_wr 80 (spZ (gi_regs D)) (gi_v D) (bv_unsigned x) ->
     mrestrict (w_H (gi_W D)) (ms_mem ms) x = mrestrict (w_H (gi_W D)) (gi_mem D) x) ->
  mem_grows (mrestrict (w_H (gi_W D)) (gi_mem D)) (mrestrict (w_H (gi_W D)) (ms_mem ms)) ->
  SRr' SEGS RZ_cf (gi_W D) (mkCfg ms mdg) (gr_post D).
Proof.
intros CTX0 D ms mdg P PLAW PCALL PEND HPD Heq HPM HS SHOK HJ K3 F3 G3.
destruct D as [ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own].
unfold gr_pre, gr_E, gr_FP, gr_post, gr_KR_kids in *.
cbn [gi_ly gi_S gi_Hp gi_W gi_regs gi_mem gi_md gi_ch gi_e gi_v gi_ty gi_num gi_str gi_kids gi_keys gi_n gi_cap
  gi_kb gi_yb gi_Lam gi_peak gi_cnt gi_fail gi_ran gi_most gi_own] in *.
destruct HPD as (HPRE & HCLOS & HCH & HROOM & HPKS & HPK24 & HHULL & H10 & Hv0 & Hv8 & HH & HSLOT & HAP & HWIN & HAT & HRA
  & HOLD & HLED & HCNT & HLIVE).
pose proof HPRE as (HPREX & HROD & HSTKHI & HRAZ0 & HFRM0).
(* the kids call's live counts (tfuzz_realloc_specX's sec_cnt / ccnt24 premises at the entry state): the text's peak
   premises bound the count at the first state of the all-granted events (PwGrowG.grow_cnt_at at j = 0), and the leaves'
   counts are those counts by conversion (grow_sec_cnt / grow_ccnt24) *)
assert (HSECk : YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV)
  by (rewrite grow_sec_cnt; exact (grow_cnt_at _ S S _ 0 _ (Permutation_refl _) HPKS)).
assert (HC24k : YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV)
  by (rewrite grow_ccnt24; exact (grow_cnt_at _ S S _ 0 _ (Permutation_refl _) HPK24)).
pose proof HPREX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : 80 <= @STK_grow prh_img_A) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hvloc : grow_vloc B ly S regs e v)
  by exact (grow_vloc_of_at B ly S Hp W mem Lam peak cnt fail ran most own regs e v HLED HAT).
destruct (grow_vbounds B ARx LAWS ly S Hp W mem md (@STK_grow prh_img_A) 80 regs e v
  HAR Hstk ltac:(lia) FS He0 Hetop Hvloc) as (Hv4096 & Hvhi & Hvstk & Hoff & Happ).
set (FP := [(v + 24, v + 40); (v + 48, v + 56)] ++
           ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))) in *.
remember (Eimg (Ereg regs (grow_extra ty kids keys n cap))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HH as ((_ & HRW) & (Hty & Vty) & _ & _ & (Hkids & Vkids) & (Hkeys & Vkeys) & (Hn & Vn) & (Hcap & Vcap)).
assert (EXn : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (grow_extra ty kids keys n cap) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EXn 4%nat ltac:(lia)) as E36. pose proof (EXn 5%nat ltac:(lia)) as E37.
pose proof (EXn 2%nat ltac:(lia)) as E34. pose proof (EXn 3%nat ltac:(lia)) as E35.
pose proof (EXn 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth grow_extra] in E34, E35, E36, E37, E38.
assert (D34 : sv_denot E (SOff 34 0) = Z_to_bv 64 kids)
  by (cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D35 : sv_denot E (SOff 35 0) = Z_to_bv 64 keys)
  by (cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 n)
  by (cbn [sv_denot]; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D37 : sv_denot E (SOff 37 0) = Z_to_bv 64 cap)
  by (cbn [sv_denot]; rewrite E37, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (U10 : bv_unsigned (ew E 10) = v).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E3 : ew E 3 = getr regs 3)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
pose proof HSLOT as (Hty56 & Hncap & Hcap0 & Hcapp).
pose proof (proj1 HJ) as HARJ.
paj_run_tok_x_inv (RUNP P PLAW) HS HJ SHOK HPM grow_Bspan.
- apply grow_awr_ok_fr with (v := v) (FR := 80);
    [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
- destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E _ W mem (ms_mem ms) mdg (ms_mem ms0) _
    (spZ regs) v FP ly S Hp W mem md ly S Hp
    ltac:(lia) FS K3 F3 G3 HAR HARJ Hceil Hslo Hshi HFr HG
    ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any _ mat)) as (K4 & F4 & G4).
  (* ---- THE KIDS CALL (A 0x86a68): a0 = kids, a1 = 56 cap', ra = the return site, s0 = v + 48 ---- *)
  assert (FS128 : 128 <= @STK_grow prh_img_A) by (apply Z.leb_le; vm_compute; reflexivity).
  assert (Hsp128 : YM05.alloc_ceiling + 128 <= spZ regs) by lia.
  assert (Hcap2 : 0 < cap2R cap <= 2 ^ 55) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
  pose proof (@cf_head_nonneg cp) as Hhd0.
  prreg HS (2%bv : bv 5) R2. prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (10%bv : bv 5) R10c. prreg HS (8%bv : bv 5) R8.
  pose proof (st_ok_restrict_reg SEGS (w_H W) E _ ms0 (11%bv : bv 5) HS) as R11c.
  change (sr_get _ (11%bv : bv 5)) with (SMd M_MUL (SOff 38 0) (SLit 56)) in R11c.
  (* the node's header at the call state (its three written fields still hold their entry values) *)
  pose proof (st_ok_region_nth SEGS E _ _ 1 grow_vA HS ltac:(vm_compute; reflexivity)) as RAc.
  pose proof (st_ok_region_nth SEGS E _ _ 2 grow_vB HS ltac:(vm_compute; reflexivity)) as RBc.
  cbn [ms_mem restrict] in RAc, RBc.
  assert (Vk0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 24) (N.to_nat 8) kids)
    by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 24 8%N (SOff 34 0) kids RAc U10);
        [cbn; tauto | exact D34 | cbn; lia | cbn; lia]).
  assert (Vy0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 32) (N.to_nat 8) keys)
    by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 32 8%N (SOff 35 0) keys RAc U10);
        [cbn; tauto | exact D35 | cbn; lia | cbn; lia]).
  assert (Vc0 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 48) (N.to_nat 8) cap)
    by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 48 8%N (SOff 37 0) cap RBc U10);
        [cbn; tauto | exact D37 | cbn; lia | cbn; lia]).
  assert (Hv0' : 0 <= v) by lia. assert (Hv64 : v + 56 <= 2 ^ 64) by lia.
  assert (HDRc : pj_hdrR SEGS (mrestrict (w_H W) (ms_mem ms0)) v ty num str kids keys n cap).
  { apply (grow_hdr_keep 80 (w_H W) mem (ms_mem ms0) (spZ regs) v ty num str kids keys n cap kids keys cap
      HH F4 G4 Hvstk Hv0' Hv64); [split; [exact Hkids | exact Vk0] | split; [exact Hkeys | exact Vy0]
      | split; [exact Hcap | exact Vc0]]. }
  (* the chain at the callee's entry: the kit's entry premise, transported (built 08:4xZ) *)
  assert (HCH2 : exists ch1, achain ly (aview SEGS (w_H W) (ms_mem ms0)) (spZ regs - 80) (v + 48) ch1).
  { destruct (Z_lt_ge_dec (v + 48) YM05.alloc_ceiling) as [Hlo48 | Hhi48].
    { exists []. apply achain_low. exact Hlo48. }
    assert (Hvsp : spZ regs <= v).
    { destruct Hvloc as [(b & m & Hinb & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | H]].
      - destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & _ & Hbc & _).
        assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
      - destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hfr).
        pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hinf) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
      - lia. }
    destruct HCH as (ch0 & Hch0). exists ch0.
    assert (HS0 : @prh_s0 prh_img_A F_grow v = v + 48) by (vm_compute; reflexivity).
    rewrite HS0 in Hch0.
    match type of Hch0 with achain _ _ ?sp0' _ _ =>
      replace (spZ regs - 80) with sp0' by (vm_compute (pi_frame F_grow); lia) end.
    refine (achain_kept_hi _ _ _ _ _ _ Hch0 ltac:(lia) _).
    intros a Ha Hb.
    pose proof (st_ok_region_nth SEGS E _ _ 1 grow_vA HS ltac:(vm_compute; reflexivity)) as RA.
    pose proof (st_ok_region_nth SEGS E _ _ 2 grow_vB HS ltac:(vm_compute; reflexivity)) as RB.
    cbn [ms_mem restrict] in RA, RB.
    assert (Vy2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 32) (N.to_nat 8) keys)
      by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 32 8%N (SOff 35 0) keys RA U10);
          [cbn; tauto | exact D35 | cbn; lia | cbn; lia]).
    assert (Vn2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 40) (N.to_nat 8) n)
      by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 40 8%N (SOff 36 0) n RB U10);
          [cbn; tauto | exact D36 | cbn; lia | cbn; lia]).
    assert (Vc2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 48) (N.to_nat 8) cap)
      by (eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 48 8%N (SOff 37 0) cap RB U10);
          [cbn; tauto | exact D37 | cbn; lia | cbn; lia]).
    destruct (Z_lt_ge_dec a (v + 40)) as [A1 | A1].
    { assert (Hx : v + 32 <= a < v + 32 + 8) by (clear - Ha A1; lia).
      exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms0) (v + 32) keys Vkeys Vy2 a Hx). }
    destruct (Z_lt_ge_dec a (v + 48)) as [A2 | A2].
    { assert (Hx : v + 40 <= a < v + 40 + 8) by (clear - A1 A2; lia).
      exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms0) (v + 40) n Vn Vn2 a Hx). }
    destruct (Z_lt_ge_dec a (v + 56)) as [A3 | A3].
    { assert (Hx : v + 48 <= a < v + 48 + 8) by (clear - A2 A3; lia).
      exact (aview_of_val_mem_eq (w_H W) mem (ms_mem ms0) (v + 48) cap Vcap Vc2 a Hx). }
    apply aview_eq_of. apply F4. unfold grow_wr.
    rewrite unsigned_lit_small by (clear - Hb H47 Htop2 Ha Hv4096; lia).
    intros [Hw | [Hw | Hw]]; clear - Hw A3 Hvsp; lia. }
  destruct HCH2 as (ch1 & Hch1).
  (* the call's register facts *)
  assert (Hsp1 : spZ (ms_regs ms0) = spZ regs + e + (-80 - e)).
  { unfold spZ at 1. rewrite R2, U2. rewrite unsigned_lit_small by lia. lia. }
  assert (H10c : getr (ms_regs ms0) 10 = w64 kids) by (rewrite R10c, E34; reflexivity).
  assert (H11c : getr (ms_regs ms0) 11 = w64 (56 * cap2R cap)).
  { rewrite R11c, denot_lit_U. unfold w64. f_equal. rewrite U_SMd, U_lit, (U_atom E 38 (cap2R cap) E38) by lia.
    cbn [zmd_raw]. unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
  assert (H8c : s0Z (ms_regs ms0) = v + 48).
  { unfold s0Z. rewrite R8, U10. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HSTKs : @STK_fuzz_realloc prh_img_A + 80 = @STK_grow prh_img_A) by (vm_compute; reflexivity).
  assert (HSTK1 : 0 <= @STK_fuzz_realloc prh_img_A) by (vm_compute; discriminate).
  (* the callee's premises at the call state *)
  assert (HROc : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms0)))
    by (apply (grow_ro_keep W mem (ms_mem ms0) (spZ regs) v HROD F4 Hoff); lia).
  assert (HLEDc : prh_ledger B ly S Hp W (ms_mem ms0) Lam peak cnt fail ran most own).
  { eapply prh_ledger_keep; [exact HLED|]. intros a Hca.
    destruct (grow_cell_apart B ARx LAWS pst_img 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
      ltac:(lia) HAR HLED HAT Hsp128 Hoff Hca) as (Ha64 & Hnw).
    apply F4. rewrite unsigned_lit_small by lia. exact Hnw. }
  assert (HUNIVm : prh_malloc_univ B).
  { eapply prh_univ_closure_malloc; [exact HCLOS | vm_compute; discriminate]. }
  destruct (prh_univ_closure_realloc B CTX0 HCLOS ltac:(vm_compute; discriminate)) as (HU1 & HU2).
  set (oldk := if cap =? 0 then [] else kb).
  assert (HOLDc : kids = 0 /\ 56 * cap = 0 /\ oldk = [] \/
                  In (kids, 56 * cap) Lam /\ bytes_at W (ms_mem ms0) kids oldk /\ Z.of_nat (length oldk) = 56 * cap).
  { subst oldk. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
    - left. destruct (Hcap0 Hc0) as (Hk0 & _). split; [exact Hk0|]. split; [lia | reflexivity].
    - right. assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
      destruct (HOLD Heq) as (Hkb & Hlkb & _). split; [exact Hin|]. split; [|exact Hlkb].
      assert (Hkp : 4096 <= kids /\ kids + 56 * cap <= 2 ^ 47).
      { pose proof HLED as (_ & _ & HFl & _).
        pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb) as (_ & Hb4096 & Hbc & _).
        assert (Hrq : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
          by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
        lia. }
      apply (grow_bytes_keep W mem (ms_mem ms0) (spZ regs) v kids kb Hkb F4); [lia | lia |].
      intros a Ha.
      assert (Hin2 : In (kids - cf_head, kids - cf_head + req_size (56 * cap + cf_head))
                       (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
      { unfold kids_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc0). cbn [app]. unfold prhReader_ab, ablocks_fp.
        cbn [map fst snd]. left. reflexivity. }
      destruct (grow_slot_apart B ARx LAWS 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap
        _ _ a ltac:(lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP Hin2) as (_ & Hnw);
        [assert (Hrq : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
           by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia); lia | exact Hnw]. }
  (* the kids realloc's live premise (tfuzz_realloc_specX, guarded by cnt <> fail): event 0 of the text's live room
     at each event (PwGrowLive.grow_room_kids) *)
  assert (HLIVEc : cnt <> fail -> blocks_bytes S + (56 * cap2R cap + cf_head) <= LIVE_MAX).
  { intros _. destruct (HLIVE Heq) as (_ & Hl). rewrite Heq in Hl. exact (grow_room_kids B ly S _ cap Hl). }
  assert (Hnmax : 56 * cap2R cap + cf_head < cf_malloc_max) by exact (proj1 (HLIVE Heq)).
  set (FP1 := if kids =? 0 then [] else ablocks_fp [(kids - cf_head, 56 * cap + cf_head)]).
  (* fpre's return-address bound for the callee: the return site is a listing slot (grow_kids_ret_ceil) *)
  assert (Hra1 : raZ (ms_regs ms0) < YM05.alloc_ceiling).
  { unfold raZ. rewrite R1. pose proof grow_kids_ret_ceil as Hslotc.
    match goal with |- bv_unsigned ?r < _ =>
      replace (bv_unsigned r) with (BASE + (GROW_OFF + 176)) by (vm_compute; reflexivity) end.
    exact Hslotc. }
  (* THE HULL (the threaded allocator hull premise): the kids call's budget is the first event of grow's
     all-granted list; the old block is NULL exactly at cap = 0 *)
  assert (HKC : kids = 0 <-> cap = 0).
  { split; [|intros Hc; exact (proj1 (Hcap0 Hc))].
    intros Hk0. destruct (Z.eq_dec cap 0) as [Hc | Hc]; [exact Hc|]. exfalso.
    assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
    pose proof HLED as (_ & _ & HFl & _).
    pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
  assert (HHUk : PresetHullBudget.hull_budget S
    (if kids =? 0 then [PresetReqAt.HMal (56 * cap2R cap + cf_head)]
     else [PresetReqAt.HRe (56 * cap + cf_head) (56 * cap2R cap + cf_head)])).
  { rewrite (grow_hull_ev kids 56 cap HKC). rewrite Heq in HHULL. exact (grow_hull_kids S (ty =? 6) cap HHULL). }
  eapply (SRr'_bind SEGS RZ_cf).
  { eapply (@aj_call_xW_spR fx rc SK SEGS B PST ARx _ LAWS (@pa_segs_low _ _ PI_prog_A) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
      W E _ ms0
      (STK_grow + e) (spZ regs + e) FP ly S Hp W mem md [] ly S Hp _ 0
      (@STK_fuzz_realloc prh_img_A) 0 FP1 (-80 - e) _ ch1
      (fQmn (ms_mem ms0) (gr_KR ly S Hp W kids (56 * cap) (56 * cap2R cap) oldk
         Lam peak cnt fail ran most own)) HS eq_refl HJ).
    - exact Hsp1.
    - rewrite Zminus_mod, He16. reflexivity.
    - lia.
    - exact HSTK1.
    - lia.
    - lia.
    - reflexivity.
    - lia.
    - rewrite R3, E3. exact Hgp.
    - rewrite R4, E4. exact Htp.
    - exact R1.
    - apply ret_ok_even. vm_compute. reflexivity.
    - apply Z.leb_le. vm_compute. reflexivity.
    - rewrite H8c. replace (spZ regs + e + (-80 - e)) with (spZ regs - 80) by lia. exact Hch1.
    - intros Hpre Hwin.
      assert (HTOPc : spZ (ms_regs ms0) + 64 <= ly_stk_hi ly) by (rewrite Hsp1; lia).
      assert (Hn0 : 0 <= 56 * cap2R cap) by lia.
      eapply (SRr'_mono SEGS RZ_cf).
      { exact (HREALLOC ly S Hp W (ms_regs ms0) (ms_mem ms0) _ ch1 kids (56 * cap)
          (56 * cap2R cap) oldk Lam peak cnt fail ran most own (conj Hpre (conj HROc (conj HTOPc (conj Hra1 HFRM0))))
          HROOM HUNIVm HSECk HC24k HHUk HU1 HU2 H10c H11c Hn0 Hnmax HLEDc HOLDc HLIVEc). }
      intros W' c' _ Hq. apply fpostW_x_of_apostR. exact Hq.
    - intros a Ha. left. subst FP1. destruct (Z.eqb_spec kids 0) as [Hk0 | Hk0].
      + destruct Ha as (r & Hr & _). destruct Hr.
      + assert (Hc : cap <> 0) by (intros Hz; apply Hk0; exact (proj1 (Hcap0 Hz))).
        destruct Ha as (r & Hr & Hrin). exists r. split; [|exact Hrin]. subst FP. apply in_or_app. right.
        unfold kids_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc). unfold prhReader_ab, ablocks_fp in *.
        cbn [app map fst snd] in *. destruct Hr as [<- | []]. left. reflexivity. }
  cbv beta. intros W2 c2 Hle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & Hc2 & HJ2 & HJ1 & HX & HP & HK).
  subst c2.
  (* the callee's m-form keep: P crosses the call (srr_inv_call) *)
  unfold fQmn in HK. destruct HK as (HK & HMN1).
  pose proof (PCALL _ _ HMN1 HPM) as HPM2. clear HPM HMN1. rename HPM2 into HPM.
  (* ---- THE RETURN SITE (A 0x86a6c): re-seat the state, the five regions kept ---- *)
  pose proof (proj1 HJ) as HARc0.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
  pose proof HJ2 as (HAR2 & _ & _ & HWLE & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
  pose proof HJ1 as (_ & _ & _ & _ & _ & HFRS1 & _ & _ & G1c & _).
  assert (HFP1s : forall r, In r FP1 -> In r (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
  { intros r Hr. subst FP1. destruct (Z.eqb_spec kids 0) as [Hk0 | Hk0]; [destruct Hr|].
    assert (Hc : cap <> 0) by (intros Hz; apply Hk0; exact (proj1 (Hcap0 Hz))).
    unfold kids_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc). unfold prhReader_ab, ablocks_fp in *.
    cbn [app map fst snd] in *. destruct Hr as [<- | []]. left. reflexivity. }
  assert (GVK : forall a, v <= a < v + 56 ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a /\ apresent (w_H W2) mem2 a).
  { exact (grow_v_kept B ARx SK LAWS ly S Hp W (ms_mem ms0) _ Lam peak cnt fail ran most own regs e v ty kids keys n cap
      _ _ FP1 ly2 S2 Hp2 W2 mem2 md2 k1 ltac:(lia) HARc0 HLEDc HAT Hsp128 Hv4096 ltac:(lia) Hoff
      ltac:(intros a Ha; apply HPRc; lia) HSLOT HAP HJ1 ltac:(lia) HFP1s). }
  assert (U241 : bv_unsigned (ew E 241) = VAL (A_OBJ 0)).
  { subst E. rewrite (Eimg_img _ 241) by (unfold A_TEXT, A_LIM; lia). apply unsigned_lit_small.
    pose proof (pa_val_range (A_OBJ 0)). unfold A_OBJ in *. lia. }
  assert (U253 : bv_unsigned (ew E 253) = VAL (A_OBJ 12)).
  { subst E. rewrite (Eimg_img _ 253) by (unfold A_TEXT, A_LIM; lia). apply unsigned_lit_small.
    pose proof (pa_val_range (A_OBJ 12)). unfold A_OBJ in *. lia. }
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARc0) as (Kcellc & _ & Kgotc & _).
  destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR2) as (Kcell2 & _ & Kgot2 & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgotc, Kgot2. rewrite (pal_cell B TL) in Kcellc, Kcell2.
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP [0; 3; 4]%nat HS2.
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q); [| specialize (HS2 HQ); clear HQ] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2; intros a Ha.
      + apply (mbyte_of_aview SEGS). apply G1c; lia.
      + intros _. apply (apresent_writable SEGS). apply HPR2. lia.
    - apply (region_kept_val_at E _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))); [exact U241 | | | lia].
      + exact (val_mem_of_rdword SEGS _ _ _ _ Kgotc).
      + exact (val_mem_of_rdword SEGS _ _ _ _ Kgot2).
    - apply (region_kept_val_at E _ _ 253 (VAL (A_OBJ 12)) 8 SHADOW_OFF); [exact U253 | | | lia].
      + exact (val_mem_of_rdword SEGS _ _ _ _ Kcellc).
      + exact (val_mem_of_rdword SEGS _ _ _ _ Kcell2). }
  rewrite <- restrict_mkst_fx in HS2.
  remember (havoc E 40 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS2.
  assert (HEI2 : img_env VAL A_LIM E2).
  { subst E2. apply img_env_havoc; [exact HEI|]. rewrite length_map. apply Nat.leb_le. reflexivity. }
  assert (AG2 : forall nn, (nn < 40)%nat -> ew E2 nn = ew E nn) by (intros nn Hnn; subst E2; apply ew_havoc_old; lia).
  assert (U2' : bv_unsigned (ew E2 2) = spZ regs) by (rewrite AG2 by lia; exact U2).
  assert (U10' : bv_unsigned (ew E2 10) = v) by (rewrite AG2 by lia; exact U10).
  assert (SHOK0 : sh_ok SEGS grow_Bx [] E2 (mrestrict (w_H W2) mem2)) by constructor.
  pose proof (proj1 HJ2) as HARr.
  paj_run_tok_x_inv (RUNP P PLAW) HS2 HJ2 SHOK0 HPM grow_Bspan.
  { apply (grow_awr_ok_stk _ _ _ 80); [lia | exact FS | exact He0 | grow_wr_stk U2']. }
  psrr_branch_tok RUN BR HS2 SHOK0 grow_Bspan.
  + (* res = 0: the kids realloc failed; return -1 *)
    lazymatch goal with Hb : branch_taken BC_EQ _ _ = true |- _ => rename Hb into Hres end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) _ |- _ => rename Hf into HFrR end.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) mem2) _ |- _ => rename Hg into HGR end.
    pose proof HJ2 as (_ & Hly2 & _).
    pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo2 & Ehi2 & _).
    assert (Hceil2 : YM05.alloc_ceiling <= ly_stk_lo ly2) by (rewrite Elo2; exact Hceil).
    assert (Hslo2 : ly_stk_lo ly2 + @STK_grow prh_img_A <= spZ regs) by (rewrite Elo2; lia).
    assert (Hshi2 : spZ regs <= ly_stk_hi ly2) by (rewrite Ehi2; lia).
    assert (HFP1in : forall a, inFP FP1 a -> inFP FP a).
    { intros a (r & Hr & Hra'). exists r. split; [subst FP; apply in_or_app; right; exact (HFP1s r Hr) | exact Hra']. }
    pose proof (cj_kept_of_journalR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (grow_OR v) HJ1) as KJ1.
    assert (KC : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_A) (spZ regs) (grow_OR v) FP ly S W mem md
                   ly2 S2 W2 mem2 md2).
    { eapply (cj_kept_transR (SK := SK) SEGS B PST ARx LAWS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf));
        [exact K4 | exact KJ1 | exact HAR | exact HARc0 | lia | lia | intros a Ha; left; exact Ha
        | intros a Ha; left; exact (HFP1in a Ha)]. }
    destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 mem2 md2 (ms_mem ms1) _
      (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
      ltac:(lia) FS KC (fun _ _ => eq_refl) (fun _ H => H) HAR HARr Hceil2 Hslo2 Hshi2 HFrR HGR
      ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat0)) as (K5 & F5 & G5).
    pose proof (proj1 HJ2) as HARr1.
    paj_run_tok_x_inv (RUNP P PLAW) HS2 HJ2 SHOK0 HPM grow_Bspan.
    { apply (grow_awr_ok_stk _ _ _ 80); [lia | exact FS | exact He0 | grow_wr_stk U2']. }
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms1)) _ |- _ => rename Hf into HFrR2 end.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms1)) _ |- _ => rename Hg into HGR2 end.
    destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 (ms_mem ms1) _ _ _
      (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
      ltac:(lia) FS K5 F5 G5 HAR HARr1 Hceil2 Hslo2 Hshi2 HFrR2 HGR2
      ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat1)) as (K6 & F6 & G6).
    pose proof HK as HKk.
    unfold fpostWmR, fpostWR.
    eapply (grow_ret B ARx SK LAWS PL_grow (@STK_grow prh_img_A) W2 E2 _ _ _ e FP regs (grow_extra ty kids keys n cap)
      ly S Hp W mem md (grow_OR v) FP ly2 S2 Hp2 _ _ ltac:(lia) HS2 eq_refl ltac:(vm_compute; reflexivity));
      [ split; [intros nn Hnn; rewrite ?AG2 by lia; subst E; rewrite ?Eimg_low by (unfold A_TEXT; lia); reflexivity
               | subst E2 E; reflexivity]
      | vm_compute; reflexivity
      | reflexivity
      | exact Hra
      | exact HJ2
      | exact K6
      | intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]
      | ].
    intros mat'. unfold fQmn. split; [|exact (PEND _ HPM)]. unfold gr_Q, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7. cbv beta.
    prreg HS2 (10%bv : bv 5) R10f.
    lazymatch type of HS2 with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := ms_mem msF) in * end.
    assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
      mrestrict (w_H W2) mF (Z_to_bv 64 a) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a)).
    { intros a Ha Hnf. subst mF. rewrite (HFrR2 (Z_to_bv 64 a)), (HFrR (Z_to_bv 64 a)); [reflexivity | |];
        rewrite unsigned_lit_small by lia; intros (r & Hin & Hr); vm_compute in Hin;
        repeat (destruct Hin as [Hin | Hin];
                [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2' in Hr; lia |]);
        contradiction. }
    assert (AVF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
      aview SEGS (w_H W2) mF a = aview SEGS (w_H W2) mem2 a) by (intros a Ha Hnf; apply aview_eq_of; exact (NW a Ha Hnf)).
    assert (PRF : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mF a).
    { intros a Ha. subst mF. eapply apresent_grows; [exact HGR2|]. eapply apresent_grows; [exact HGR | exact Ha]. }
    assert (HDRF : pj_hdrR SEGS (mrestrict (w_H W2) mF) v ty num str kids keys n cap).
    { apply (pj_hdr_aview (w_H W) (w_H W2) (ms_mem ms0) mF v ty num str kids keys n cap HDRc).
      intros a Ha. destruct (GVK a Ha) as (Ea & Pa). split; [rewrite AVF by lia; exact Ea | exact (PRF a Pa)]. }
    assert (HLK : forall Hp' pk cn fl rn, prh_ledger B ly2 S2 Hp' W2 mem2 Lam pk cn fl rn most own ->
                   prh_ledger B ly2 S2 Hp' W2 mF Lam pk cn fl rn most own).
    { intros Hp' pk cn fl rn HL2. eapply prh_ledger_keep; [exact HL2|]. intros a Hca.
      destruct (grow_cell_apart B ARx LAWS pst_img 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
        ltac:(lia) HAR HLED HAT Hsp128 Hoff Hca) as (Ha64 & Hnw).
      apply NW; [lia | unfold grow_wr in Hnw; lia]. }
    pose proof (pal_env B TL) as ((Her0 & Her1) & _).
    assert (HER : forall w, rd32 (aview SEGS (w_H W2) mem2) (as_errno B) w -> rd32 (aview SEGS (w_H W2) mF) (as_errno B) w).
    { intros w Hw. apply (rd32_aview _ _ _ _ Hw). intros x Hx. apply AVF; unfold kLowMemEnd in Her1; lia. }
    assert (HKB2 : bytes_at W2 mem2 kids kb -> bytes_at W2 mF kids kb).
    { intros Hb. apply (bytes_at_aview W2 W2 mem2 mF kids kb Hb). intros a Ha.
      destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
      - destruct (HOLD Heq) as (_ & Hlk & _). rewrite Hc0 in Hlk. lia.
      - assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
        destruct (HOLD Heq) as (_ & Hlk & _).
        pose proof HLED as (_ & _ & HFl & _).
        pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & Hbc & _).
        assert (Hrq : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
          by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
        apply AVF; lia. }
    assert (Hkb0 : cap = 0 -> bytes_at W2 mF kids kb).
    { intros Hc0. destruct (HOLD Heq) as (_ & Hlk & _). rewrite Hc0 in Hlk.
      destruct kb; [intros j Hj; cbn in Hj; lia | cbn in Hlk; lia]. }
    assert (Hyb0 : cap = 0 -> ty = 6 -> bytes_at W2 mF keys yb).
    { intros Hc0 H6. destruct (HOLD Heq) as (_ & _ & HY). destruct (HY H6) as (_ & Hly). rewrite Hc0 in Hly.
      destruct yb; [intros j Hj; cbn in Hj; lia | cbn in Hly; lia]. }
    assert (HYB2 : cap <> 0 -> ty = 6 -> In (keys - cf_head, 8 * cap + cf_head) (ablocks B ly2 S2) ->
                   bytes_at W2 mF keys yb).
    { intros Hc0 H6 Hin2.
      assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hink & Hky). specialize (Hky H6).
      unfold prh_lin in Hink, Hky.
      destruct (HOLD Heq) as (_ & _ & HY). destruct (HY H6) as (Hyb & Hly).
      pose proof HLED as (_ & HND & HFl & _).
      pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hbk & _). cbn [fst snd] in Hk, Hbk.
      pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hink) as (Hk' & Hbkid & _). cbn [fst snd] in Hk', Hbkid.
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & Hb4096 & Hbc & _).
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbkid) as (_ & Hb4096' & Hbc' & _).
      assert (Hrqk : 8 * cap + cf_head <= req_size (8 * cap + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (8 * cap + cf_head) 0); lia).
      assert (Hrqd : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
      assert (Hkk : kids <> keys).
      { intros Ekk. subst keys. assert (E56 : 56 * cap = 8 * cap) by exact (nodup_fst_eq Lam kids _ _ HND Hink Hky).
        lia. }
      assert (Hne : (keys - cf_head, 8 * cap + cf_head) <> (kids - cf_head, 56 * cap + cf_head))
        by (intros Heqb; injection Heqb; intros; lia).
      pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbk Hbkid Hne) as Hdis.
      unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
      assert (Hyc : bytes_at W (ms_mem ms0) keys yb).
      { apply (grow_bytes_keep W mem (ms_mem ms0) (spZ regs) v keys yb Hyb F4); [lia | lia |].
        intros a Ha.
        assert (Hin2' : In (keys - cf_head, keys - cf_head + req_size (8 * cap + cf_head))
                          (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
        { unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), (proj2 (Z.eqb_eq ty 6) H6).
          cbn [orb negb app]. unfold prhReader_ab, ablocks_fp. cbn [map fst snd]. right; left; reflexivity. }
        destruct (grow_slot_apart B ARx LAWS 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap
          _ _ a ltac:(lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP Hin2') as (_ & Hnw); [lia | exact Hnw]. }
      assert (Hy2 : bytes_at W2 mem2 keys yb).
      { apply (bytes_at_aview W W2 (ms_mem ms0) mem2 keys yb Hyc). intros a Ha.
        pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2c & _).
        replace a with ((keys - cf_head) + (a - (keys - cf_head))) by lia.
        apply (G2c _ _ _ Hbk Hin2); [lia|].
        intros ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi. subst FP1.
        rewrite (proj2 (Z.eqb_neq kids 0)) in Hr by lia. unfold ablocks_fp in Hr. cbn [map fst snd In] in Hr.
        destruct Hr as [Hr | []]. injection Hr as <- <-. lia. }
      apply (bytes_at_aview W2 W2 mem2 mF keys yb Hy2). intros a Ha. apply AVF; lia. }
    pose proof HLED as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt0 & _) & _). (* prh_glob ef7c8ca98529: + prh_most, prh_own *)
    assert (Hcnt1 : (cnt + 1) mod 2 ^ 64 = cnt + 1) by (apply Z.mod_small; lia).
    assert (Hheld : 0 <= PRH_Charge.prh_held (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)).
    { rewrite Heq, grow_held_eq by lia. unfold cap2R. destruct (Z.eqb_spec cap 0); destruct (ty =? 6); lia. }
    destruct HK as (res & H10r & HROOM2 & HHU1 & POS0 & POSM & POSR & OUTM & OUTR & ARMS).
    assert (HHUk1 : PresetHullBudget.hull_used S S2 [prhPg_ev 56 cap])
      by (rewrite <- (grow_hull_ev kids 56 cap HKC); exact HHU1).
    assert (E44 : ew E2 44 = getr regs2 10).
    { subst E2. change 44%nat with (40 + 4)%nat.
      rewrite (ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia).
      reflexivity. }
    assert (Hres0 : bv_unsigned (getr regs2 10) = 0).
    { rewrite branch_eq_U in Hres. apply Z.eqb_eq in Hres. rewrite U_lit in Hres by lia.
      rewrite U_SOff, E44, Z.add_0_r in Hres. unfold zcanon, M64 in Hres. rewrite Z.mod_small in Hres; [exact Hres|].
      apply u64_range. }
    rewrite H10r in Hres0. unfold w64 in Hres0.
    (* the result is NULL on every arm this branch can take: the two SUCCESS shapes put the new block below the
       ceiling, and a block base is at least 4096 + cf_head *)
    assert (HresN : forall res', 4096 + cf_head <= res' -> In (res' - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2) ->
      bv_unsigned (Z_to_bv 64 res) = 0 -> res' = res -> False).
    { intros res' H4096 Hin2 Hz Her. subst res'.
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hbc & _).
      assert (Hrq0 : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
      rewrite unsigned_lit_small in Hz by lia. lia. }
    assert (HresZ : res = 0).
    { destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
      - assert (Hk0 : kids = 0) by exact (proj1 (Hcap0 Hc0)).
        destruct ARMS as [(_ & HAP0) | [(Hp0 & _) | [(Hp0 & _) | (Hp0 & _)]]]; [| lia | lia | lia].
        destruct HAP0 as [(_ & Hz & _) | [(_ & Hz & _) | (Hcf & Hrs & _ & _ & _ & Eab & _)]]; [exact Hz | exact Hz |].
        exfalso. exact (HresN res Hrs ltac:(rewrite Eab; apply in_or_app; right; left; reflexivity) Hres0 eq_refl).
      - assert (Hkids0 : kids <> 0).
        { assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
          pose proof HLED as (_ & _ & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
        destruct ARMS as [(Hp0 & _) | [(_ & _ & Hz & _) | [(_ & _ & Hz & _) |
          (_ & _ & Hrs & _ & l1 & l2 & _ & _ & _ & (b1 & b2 & _ & _ & Hperm) & _)]]];
          [exfalso; exact (Hkids0 Hp0) | exact Hz | exact Hz |].
        exfalso. exact (HresN res Hrs (Permutation_in _ (Permutation_sym Hperm) (or_introl eq_refl)) Hres0 eq_refl). }
    (* fuzz_realloc's NULL (outcomes [false]): no event, the position kept (the leaf's post-implication at res = 0) *)
    assert (HPOS0 : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap [false]) ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (prhPg_evs (ty =? 6)%Z n cap [false]))%nat
          H0 hist' S2)
      by (rewrite Heq, grow_evs_false; exact (POS0 HresZ)).
    (* THE OUTCOME EXCLUSION of the refused arm (the text's refused arm, PRH_Base's THE OUTCOME UNDER THE RUN
       HYPOTHESIS): at a model run whose next events are the all-granted ones with consumer allocations, the kids
       realloc's own outcome clause (cnt <> fail) says the instance granted, but res = 0 *)
    assert (HEXK : cnt <> fail -> forall (sm : list Z -> Z * Z) (x : list Z)
        (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap []) ->
        PRH_Base.prh_cons_from sm x os i (length (prhPg_evs (ty =? 6) n cap [])) -> False).
    { intros Hcf0 sm x os i H0 hist Hpos Hrun Hcons. rewrite Heq, grow_evs_all in Hrun, Hcons.
      apply (proj1 (PRH_Base.prh_run_at_app_iff sm x os i [prhPg_ev 56 cap] _)) in Hrun as (Hr1 & _).
      apply (proj1 (PRH_Base.prh_cons_from_app_iff sm x os i 1 _)) in Hcons as (Hc1 & _).
      revert Hr1. unfold prhPg_ev. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; intros Hr1.
      - destruct (OUTM (proj1 (Hcap0 Hc0)) sm x os i H0 hist Hpos Hr1 Hc1 Hcf0) as (Hrn & _). exact (Hrn HresZ).
      - assert (Hk0n : kids <> 0).
        { assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
          pose proof HLED as (_ & _ & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
        destruct (OUTR Hk0n sm x os i H0 hist Hpos Hr1 Hc1 Hcf0) as (Hrn & _). exact (Hrn HresZ). }
    (* THE OUTCOME OF AN INJECTED READING (DEAD_PJPARSE), the same leaf outcome at the model's grant list okk
       (PwGrowG.grow_excl_of_leaf) *)
    assert (HEXJ : cnt <> fail -> forall (sm : list Z -> Z * Z) (x : list Z)
        (os : list (option nat * option nat * option nat)) (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt)))) ->
        PRH_Base.prh_cons_from sm x os i
          (length (prhPg_evs (ty =? 6) n cap (PresetReqAt.okk (Z.to_nat (fail - cnt))))) ->
        cnt <= fail < cnt + Z.of_nat (PjGrammar.calls (PRH_Charge.prhPg_gtrace (ty =? 6) n cap)) -> False).
    { intros Hcf0. apply (grow_excl_of_leaf (ty =? 6) n cap cnt fail S res Heq Hcf0 HresZ).
      intros sm x os i H0 hist Hpos Hr1 Hc1 Hcf1. revert Hr1 Hc1. unfold prhPg_ev.
      destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; intros Hr1 Hc1.
      - exact (proj1 (OUTM (proj1 (Hcap0 Hc0)) sm x os i H0 hist Hpos Hr1 Hc1 Hcf1)).
      - assert (Hk0n : kids <> 0).
        { assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
          pose proof HLED as (_ & _ & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
        exact (proj1 (OUTR Hk0n sm x os i H0 hist Hpos Hr1 Hc1 Hcf1)). }
    split; [exact HROOM2|].
    split; [rewrite Heq; exact (grow_hull_one S S2 (ty =? 6) cap HHUk1)|].
    destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
    { (* cap = 0: kids = 0, the realloc is fuzz_malloc's post *)
      assert (Hk0 : kids = 0) by exact (proj1 (Hcap0 Hc0)).
      destruct ARMS as [(_ & HAP0) | [(Hp0 & _) | [(Hp0 & _) | (Hp0 & _)]]]; [| lia | lia | lia].
      destruct HAP0 as [(Hcf & Hr0 & EHp & Eab & HL2) | [(Hcf & Hr0 & EHp & Eab & HNULL & HER2 & HL2) | (Hcf & Hrs & _ & _ & _ & Eab & _)]].
      - split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; lia|].
        right; left. split; [exact Heq|]. split; [exact Hcf|]. split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
        split; [exact EHp|]. split; [exact Eab|].
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; reflexivity|]. split; [rewrite Hcnt1 in HL2; exact (HLK _ _ _ _ _ HL2)|].
        split; [exact HDRF|]. split; [exact (Hkb0 Hc0)|]. split; [exact (Hyb0 Hc0) | split; [rewrite Heq, grow_evs_false; exact (grow_live_keep B _ _ _ _ Eab) | exact HPOS0]].
      - split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; lia|].
        right; right; left. split; [exact Heq|]. split; [exact Hcf|]. split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
        split; [rewrite EHp; apply Permutation_refl|]. split; [exact Eab|].
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; reflexivity|]. 
        split; [destruct HNULL as (rgc & mc & dc & Wc0 & cc0 & HNULL0); exact (grow_null_wf B _ _ _ _ _ _ _ _ _ _ _ HNULL0)|].
        split; [exact (HER _ HER2)|].
        split; [exact (HEXK Hcf)|]. split; [exact (HEXJ Hcf)|].
        (* the ledger: the text's cap = 0 case, prh_alloc_post's refused arm verbatim *)
        split; [exact (HLK _ _ _ _ _ HL2)|].
        split; [exact HDRF|]. split; [exact (Hkb0 Hc0)|]. split; [exact (Hyb0 Hc0) | split; [rewrite Heq, grow_evs_false; exact (grow_live_keep B _ _ _ _ Eab) | exact HPOS0]].
      - exfalso. assert (Hin2 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2))
          by (rewrite Eab; apply in_or_app; right; left; reflexivity).
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hbc & _).
        assert (Hrq0 : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
          by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
        rewrite unsigned_lit_small in Hres0 by lia. lia. }
    { (* cap <> 0: kids is a live harness block *)
      assert (Hkids0 : kids <> 0).
      { assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
        pose proof HLED as (_ & _ & HFl & _).
        pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
      assert (Eold : oldk = kb) by (subst oldk; destruct (Z.eqb_spec cap 0); [lia | reflexivity]).
      destruct ARMS as [(Hp0 & _) | [(_ & Hcf & Hr0 & EHp & Eab & Hold2 & HL2) |
        [(_ & Hcf & Hr0 & EHp & Eab & Hold2 & HNULL & HER2 & HL2) | (_ & Hcf & Hrs & _ & l1 & l2 & _ & _ & _ & (b1 & b2 & _ & _ & Hperm) & _)]]];
        [exfalso; exact (Hkids0 Hp0) | | | ].
      - assert (Hinky : ty = 6 -> In (keys - cf_head, 8 * cap + cf_head) (ablocks B ly2 S2)).
        { intros H6. rewrite Eab. assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (_ & Hky).
          pose proof HLED as (_ & _ & HFl & _).
          exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) (Hky H6)))). }
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; lia|].
        right; left. split; [exact Heq|]. split; [exact Hcf|]. split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
        split; [exact EHp|]. split; [exact Eab|].
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; reflexivity|]. split; [rewrite Hcnt1 in HL2; exact (HLK _ _ _ _ _ HL2)|].
        split; [exact HDRF|]. split; [rewrite Eold in Hold2; exact (HKB2 Hold2)|].
        split; [intros H6; exact (HYB2 Hc0 H6 (Hinky H6)) | split; [rewrite Heq, grow_evs_false; exact (grow_live_keep B _ _ _ _ Eab) | exact HPOS0]].
      - assert (Hinky : ty = 6 -> In (keys - cf_head, 8 * cap + cf_head) (ablocks B ly2 S2)).
        { intros H6. rewrite Eab. assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (_ & Hky).
          pose proof HLED as (_ & _ & HFl & _).
          exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) (Hky H6)))). }
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; lia|].
        right; right; left. split; [exact Heq|]. split; [exact Hcf|]. split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
        split; [exact EHp|]. split; [exact Eab|].
        split; [rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab; reflexivity|]. 
        split; [exact HNULL|]. split; [exact (HER _ HER2)|].
        split; [exact (HEXK Hcf)|]. split; [exact (HEXJ Hcf)|].
        split; [exact (HLK _ _ _ _ _ HL2)|].
        split; [exact HDRF|]. split; [rewrite Eold in Hold2; exact (HKB2 Hold2)|].
        split; [intros H6; exact (HYB2 Hc0 H6 (Hinky H6)) | split; [rewrite Heq, grow_evs_false; exact (grow_live_keep B _ _ _ _ Eab) | exact HPOS0]].
      - exfalso. assert (Hin2 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2))
          by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & Hbc & _).
        assert (Hrq0 : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
          by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
        rewrite unsigned_lit_small in Hres0 by lia. lia. }
  + (* res <> 0: the kids moved; store them at v + 24, re-read v's shadow, go on to the ty = 6 test *)
    lazymatch goal with Hb : branch_taken BC_EQ _ _ = false |- _ => rename Hb into Hres end.
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) mem2) _ |- _ => rename Hf into HFrR end.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) mem2) _ |- _ => rename Hg into HGR end.
    pose proof HJ2 as (_ & Hly2 & _).
    pose proof Hly2 as (_ & _ & _ & _ & _ & ElyF & _ & _ & _ & Elo2 & Ehi2 & _).
    pose proof HJ1 as (_ & _ & _ & _ & _ & Hfrs1 & _).
    assert (Hceil2 : YM05.alloc_ceiling <= ly_stk_lo ly2) by (rewrite Elo2; exact Hceil).
    assert (Hslo2 : ly_stk_lo ly2 + @STK_grow prh_img_A <= spZ regs) by (rewrite Elo2; lia).
    assert (Hshi2 : spZ regs <= ly_stk_hi ly2) by (rewrite Ehi2; lia).
    assert (Efrs : frames S2 = frames S) by (rewrite Hfrs1; reflexivity).
    assert (Efa2 : forall cid pos, frame_addr ly2 cid pos = frame_addr ly cid pos)
      by (intros cid pos; unfold frame_addr; rewrite ElyF; reflexivity).
    (* the node's header and its presence at the post state *)
    assert (HDR2 : pj_hdrR SEGS (mrestrict (w_H W2) mem2) v ty num str kids keys n cap)
      by exact (pj_hdr_aview (w_H W) (w_H W2) (ms_mem ms0) mem2 v ty num str kids keys n cap HDRc GVK).
    (* the callee's footprint is a heap block, so every byte of it is an app address *)
    assert (HFPapp : forall a, inFP FP1 a -> app_addr a).
    { intros a (r & Hr & Hra'). subst FP1. destruct (Z.eqb_spec kids 0) as [Hk0 | Hk0]; [destruct Hr|].
      unfold ablocks_fp in Hr. cbn [map fst snd In] in Hr. destruct Hr as [<- | []].
      cbn [fst snd] in Hra'.
      assert (Hcp : cap <> 0) by (intros Hz; apply Hk0; exact (proj1 (Hcap0 Hz))).
      assert (Hcp0 : 0 < cap) by lia. destruct (Hcapp Hcp0) as (Hink & _). unfold prh_lin in Hink.
      pose proof HLED as (_ & _ & HFl & _).
      pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hink) as (_ & Hbkid & _). cbn [fst snd] in Hbkid.
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbkid) as (_ & _ & _ & Hiapp & _).
      exact (in_app_addr _ _ a Hiapp ltac:(lia)). }
    (* the ledger's block clause at the entry state, as grow_at_kept takes it *)
    assert (HLAMb : forall a kk, In (a, kk) Lam -> In (a - cf_head, kk + cf_head) (ablocks B ly S)).
    { intros a kk Hin. pose proof HLED as (_ & _ & HFl & _).
      exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFl (a, kk) Hin))). }
    pose proof HK as HKk.
    destruct HK as (res & H10r & HROOM2 & HHU1 & POS0 & POSM & POSR & OUTM & OUTR & ARMS).
    assert (HHUk1 : PresetHullBudget.hull_used S S2 [prhPg_ev 56 cap])
      by (rewrite <- (grow_hull_ev kids 56 cap HKC); exact HHU1).
    assert (E44 : ew E2 44 = getr regs2 10).
    { subst E2. change 44%nat with (40 + 4)%nat.
      rewrite (ew_havoc_new E 40 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia).
      reflexivity. }
    assert (Hkids0' : cap <> 0 -> kids <> 0).
    { intros Hc0. assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
      pose proof HLED as (_ & _ & HFl & _).
      pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
      destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
    assert (Hresne : res <> 0).
    { intros Hz. rewrite branch_eq_U in Hres. apply Z.eqb_neq in Hres. apply Hres.
      rewrite (U_lit E2 0) by lia. rewrite U_SOff, E44, H10r, Hz. unfold w64.
      rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
      first [reflexivity | (unfold zcanon, M64; reflexivity)]. }
    pose proof HLED as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hcnt0 & _) & _). (* prh_glob ef7c8ca98529: + prh_most, prh_own *)
    assert (Hcnt1 : (cnt + 1) mod 2 ^ 64 = cnt + 1) by (apply Z.mod_small; lia).
    assert (Hkb_len : Z.of_nat (length kb) = 56 * cap) by exact (proj1 (proj2 (HOLD Heq))).
    pose proof asan_consts as (C1' & _).
    assert (Hsp0 : YM05.alloc_ceiling <= spZ regs) by lia.
    (* ---- WHAT THE KIDS CALL LEFT, in one form for its two shapes (cap = 0: fuzz_malloc's post, kids NULL;
       cap <> 0: fuzz_realloc's SUCCESS arm): the harness list, the blocks and the hidden heads with the new block
       in place of the old one, the ledger, the node's place, the node apart from the new block, the old bytes at the
       new block and its shadow facts ---- *)
    assert (COM : exists Lr blr hlr,
      Permutation Lam (kids_blkR kids cap ++ Lr) /\
      Permutation (ablocks B ly S) (prhReader_ab (kids_blkR kids cap) ++ blr) /\
      Permutation (ablocks B ly2 S2) ((res - cf_head, 56 * cap2R cap + cf_head) :: blr) /\
      Permutation Hp (prhReader_hd (kids_blkR kids cap) ++ hlr) /\ Hp2 = (res - cf_head) :: hlr /\
      prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, 56 * cap2R cap) :: Lr)
        (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (cnt + 1) fail ran most own /\
      prhReader_at B ly2 S2 ((res, 56 * cap2R cap) :: Lr) regs e v 56 /\
      (forall x, res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head) -> ~ (v <= x < v + 56)) /\
      bytes_at W2 mem2 res kb /\ prhReader_vis W2 mem2 res (56 * cap2R cap) /\
      4096 + cf_head <= res /\ res mod 16 = 0 /\ cnt <> fail /\
      blocks_bytes S2 <= blocks_bytes S + 56 * (cap2R cap - cap) + cf_head).
    { destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
      - (* cap = 0: fuzz_malloc's post *)
        assert (Hk0 : kids = 0) by exact (proj1 (Hcap0 Hc0)).
        assert (Ekb : kids_blkR kids cap = []) by (unfold kids_blkR; rewrite (proj2 (Z.eqb_eq cap 0) Hc0); reflexivity).
        destruct ARMS as [(_ & HAP0) | [(Hp0 & _) | [(Hp0 & _) | (Hp0 & _)]]];
          [| exfalso; exact (Hp0 Hk0) | exfalso; exact (Hp0 Hk0) | exfalso; exact (Hp0 Hk0)].
        destruct HAP0 as [(_ & Hr0 & _) | [(_ & Hr0 & _) |
          (Hcf & Hr16 & Hrm & Hnin & EHp2 & Eab2 & HRA2 & HVIS2 & (lnew & Hlnew & Hbnew) & HL2)]];
          [exfalso; exact (Hresne Hr0) | exfalso; exact (Hresne Hr0) |].
        assert (Ekb0 : kb = []) by (destruct kb; [reflexivity | cbn [length] in Hkb_len; lia]).
        assert (Hnn0 : 0 <= 56 * cap2R cap) by lia.
        assert (Hnh0 : 0 <= 56 * cap2R cap + cf_head) by lia.
        pose proof (grow_alloc_fresh ly S ly2 S2 Hp2 W2 mem2 md2 (res - cf_head) (56 * cap2R cap + cf_head) HAR2
          Hnh0 Eab2) as Hfresh0.
        assert (HAT2 : prhReader_at B ly2 S2 ((res, 56 * cap2R cap) :: Lam) regs e v 56)
          by exact (grow_at_kept0 B ARx ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v (56 * cap2R cap) res HAR
                      HAR2 HAT Eab2 Efrs Efa2 Hfresh0).
        assert (HAPn : forall x, res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head) ->
                         ~ (v <= x < v + 56))
          by exact (grow_new_apart0 ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v (56 * cap2R cap) res HAR HAR2
                      HLAMb HAT Eab2 Efrs Efa2 Hsp0 Hnn0).
        assert (HL2' : prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, 56 * cap2R cap) :: Lam)
                         (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lam))) (cnt + 1) fail ran most own).
        { replace (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lam)))
            with (Z.max peak (Ledger.lsum Lam + 56 * cap2R cap)) by (cbn [Ledger.lsum]; lia).
          rewrite <- Hcnt1. exact HL2. }
        exists Lam, (ablocks B ly S), Hp. rewrite Ekb. unfold prhReader_ab, prhReader_hd. cbn [map app].
        split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
        split; [rewrite Eab2; apply Permutation_sym, Permutation_cons_append|].
        split; [apply Permutation_refl|]. split; [exact EHp2|].
        split; [exact HL2'|]. split; [exact HAT2|]. split; [exact HAPn|].
        split; [rewrite Ekb0; intros j Hj; cbn [length] in Hj; lia|].
        split; [split; [exact HRA2 | exact HVIS2]|].
        split; [exact Hr16|]. split; [exact Hrm|]. split; [exact Hcf|].
        rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), Eab2, bsum_app. cbn [bsum fold_right snd].
        rewrite Hc0. unfold cap2R. cbn [Z.eqb]. lia.
      - (* cap <> 0: fuzz_realloc's SUCCESS arm *)
        assert (Hcp : 0 < cap) by lia.
        assert (Hkids0 : kids <> 0).
        { destruct (Hcapp Hcp) as (Hin & _). unfold prh_lin in Hin.
          pose proof HLED as (_ & _ & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hin) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). lia. }
        assert (Eold : oldk = kb) by (subst oldk; destruct (Z.eqb_spec cap 0); [lia | reflexivity]).
        assert (Ekb : kids_blkR kids cap = [(kids, 56 * cap)])
          by (unfold kids_blkR; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity).
        destruct ARMS as [(Hp0 & _) | [(_ & _ & Hr0 & _) | [(_ & _ & Hr0 & _) |
          (_ & Hcf & Hr16 & Hrm & l1 & l2 & ELam & Hnin & EHp2 & (b1 & b2 & Eab & Hfresh & Hperm) & (rest & Hlr & Hbr)
           & HRA2 & HVIS2 & HL2)]]];
          [exfalso; exact (Hkids0 Hp0) | exfalso; exact (Hresne Hr0) | exfalso; exact (Hresne Hr0) |].
        assert (Hin_k : In (kids, 56 * cap) Lam) by (rewrite ELam; apply in_or_app; right; left; reflexivity).
        assert (HAPk : forall x, pj_holdsR (kids, 56 * cap) x -> ~ (v <= x < v + 56)).
        { intros x Hx. apply (HAP (kids, 56 * cap) x); [rewrite Ekb; apply in_or_app; left; left; reflexivity | exact Hx]. }
        assert (HAT2 : prhReader_at B ly2 S2 ((res, 56 * cap2R cap) :: l1 ++ l2) regs e v 56)
          by exact (grow_at_kept B ARx ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam l1 l2 regs e v kids (56 * cap)
                      (56 * cap2R cap) res b1 b2 HAR HAR2 HLAMb HAT HAPk ELam Eab Hperm Efrs Efa2 Hfresh).
        assert (HAPn : forall x, res - cf_head <= x < res - cf_head + req_size (56 * cap2R cap + cf_head) ->
                         ~ (v <= x < v + 56))
          by exact (grow_new_apart ly S Hp W mem md ly2 S2 Hp2 W2 mem2 md2 Lam regs e v kids (56 * cap) (56 * cap2R cap)
                      res b1 b2
                      HAR HAR2 HLAMb HAT HAPk Hin_k Eab Hperm Efrs Efa2 Hfresh Hsp0).
        assert (HL2' : prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, 56 * cap2R cap) :: l1 ++ l2)
                         (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2))) (cnt + 1) fail ran most own).
        { replace (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: l1 ++ l2)))
            with (Z.max peak (Ledger.lsum (l1 ++ l2) + 56 * cap2R cap)) by (cbn [Ledger.lsum]; lia).
          rewrite <- Hcnt1. exact HL2. }
        assert (Hc2c : cap2R cap = 2 * cap) by (unfold cap2R; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity).
        assert (HB2 : bytes_at W2 mem2 res kb).
        { rewrite Eold, Z.min_l, firstn_all2 in Hbr by lia. exact (bytes_at_prefix W2 mem2 res kb rest Hbr). }
        assert (HhpIn : In (kids - cf_head) Hp).
        { pose proof HLED as (_ & _ & HFl & _).
          exact (proj1 (proj2 (proj2 (proj1 (Forall_forall _ _) HFl _ Hin_k)))). }
        exists (l1 ++ l2), (b1 ++ b2), (remove Z.eq_dec (kids - cf_head) Hp).
        rewrite Ekb. unfold prhReader_ab, prhReader_hd. cbn [map app fst snd].
        split; [rewrite ELam; apply Permutation_sym, Permutation_middle|].
        split; [rewrite Eab; apply Permutation_sym, Permutation_middle|].
        split; [exact Hperm|].
        split; [exact (perm_remove_nodup Hp _ (ledger_hp_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HLED) HhpIn)|].
        split; [exact EHp2|].
        split; [exact HL2'|]. split; [exact HAT2|]. split; [exact HAPn|]. split; [exact HB2|].
        split; [split; [exact HRA2 | exact HVIS2]|].
        split; [exact Hr16|]. split; [exact Hrm|]. split; [exact Hcf|].
        rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm), Eab, !bsum_app,
          !bsum_cons, !bsum_app. cbn [snd]. lia. }
    destruct COM as (Lr & blr & hlr & PLam & PAB1 & PAB2 & PHP & EHp2 & HL2 & HAT2 & HAPn & HB2 & HVIS2 & Hr16 & Hrm
      & Hcf & HBB2).
    (* ---- the node at the post state: its shadow (grow_v_shadow2), its place for the runs (grow_vloc2) ---- *)
    pose proof (EXn 0%nat ltac:(lia)) as E32. pose proof (EXn 1%nat ltac:(lia)) as E33.
    cbn [Nat.add nth grow_extra] in E32, E33.
    assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
    assert (U32' : bv_unsigned (ew E2 32) = SHADOW_OFF) by (rewrite AG2 by lia; exact U32).
    assert (HRAc : range_addressable (aview SEGS (w_H W) (ms_mem ms0)) SHADOW_OFF v 56).
    { pose proof SHOK as SH0. unfold sh_ok, grow_SH in SH0. apply Forall_inv in SH0. destruct SH0 as (HR & _).
      unfold grow_Bx in HR. cbn [she_m she_lo she_hi] in HR.
      rewrite !U_SOff, U32, U10, !Z.add_0_r, !zcanon_id in HR by (unfold M64, SHADOW_OFF; lia).
      exact HR. }
    assert (Hlo2 : ly_stk_lo ly2 <= spZ regs) by lia.
    assert (Hhi2 : spZ regs + e <= ly_stk_hi ly2) by (rewrite Ehi2; lia).
    assert (HRA2v : range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF v 56)
      by exact (grow_v_shadow2 B ARx SK LAWS ly S Hp W (ms_mem ms0) _ ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v _ _ FP1 k1
                  HARc0 HAR2 HL2 HAT2 Hlo2 Hhi2 HRAc HJ1 HFPapp).
    assert (Hvloc2 : grow_vloc B ly2 S2 regs e v)
      by exact (grow_vloc2 B ARx SK LAWS ly S Hp W (ms_mem ms0) _ Lam peak cnt fail ran most own regs e v ty kids keys n cap _ _
                  FP1 ly2 S2 Hp2 W2 mem2 md2 k1 ltac:(lia) HARc0 HLEDc HAT Hsp128 HSLOT HAP HJ1 HFP1s).
    (* ---- the memory at ms1: only grow's frame changed since the call ---- *)
    assert (NW1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
      mrestrict (w_H W2) (ms_mem ms1) (Z_to_bv 64 a) = mrestrict (w_H W2) mem2 (Z_to_bv 64 a)).
    { intros a Ha Hnf. rewrite (HFrR (Z_to_bv 64 a)); [reflexivity|].
      rewrite unsigned_lit_small by lia. intros (r & Hin & Hr). vm_compute in Hin.
      repeat (destruct Hin as [Hin | Hin];
              [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2' in Hr; lia |]).
      contradiction. }
    assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
      aview SEGS (w_H W2) (ms_mem ms1) a = aview SEGS (w_H W2) mem2 a)
      by (intros a Ha Hnf; apply aview_eq_of; exact (NW1 a Ha Hnf)).
    assert (PR1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
      by (intros a Ha; eapply apresent_grows; [exact HGR | exact Ha]).
    assert (HDR1 : pj_hdrR SEGS (mrestrict (w_H W2) (ms_mem ms1)) v ty num str kids keys n cap).
    { apply (pj_hdr_aview (w_H W) (w_H W2) (ms_mem ms0) (ms_mem ms1) v ty num str kids keys n cap HDRc).
      intros a Ha. destruct (GVK a Ha) as (Ea & Pa). split; [rewrite AV1 by lia; exact Ea | exact (PR1 a Pa)]. }
    assert (HRA1 : range_addressable (aview SEGS (w_H W2) (ms_mem ms1)) SHADOW_OFF v 56).
    { intros x Hx. destruct (HRA2v x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
      assert (Hq : 0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      unfold shadow_of_addr in *. rewrite AV1; [exact Hs | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]. }
    (* ---- the re-seat: the node's two regions back, the shadow entry back ---- *)
    assert (Hd0 : v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v)
      by exact (range_apart_img _ _ (cell_img (VAL (A_OBJ 0)) (or_introl eq_refl)) Hoff).
    assert (Hd12 : v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v)
      by exact (range_apart_img _ _ (cell_img (VAL (A_OBJ 12)) (or_intror eq_refl)) Hoff).
    assert (U241' : bv_unsigned (ew E2 241) = VAL (A_OBJ 0))
      by (subst E2; rewrite ew_havoc_hi by (rewrite length_map; cbn; lia); exact U241).
    assert (U253' : bv_unsigned (ew E2 253) = VAL (A_OBJ 12))
      by (subst E2; rewrite ew_havoc_hi by (rewrite length_map; cbn; lia); exact U253).
    pose proof HDR1 as ((_ & HRW1) & (_ & Vty1) & _ & _ & (_ & Vk1) & (_ & Vy1) & (_ & Vn1) & (_ & Vc1)).
    assert (DV2 : forall k w, (k < 40)%nat -> ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
      sv_denot E2 (SOff k 0) = Z_to_bv 64 w).
    { intros k w Hk Hkw Hw. cbn [sv_denot]. rewrite AG2 by exact Hk. rewrite Hkw, unsigned_lit_small by exact Hw.
      rewrite Z.add_0_r. reflexivity. }
    assert (RB1 : region_ok SEGS E2 (mrestrict (w_H W2) (ms_mem ms1)) grow_vB).
    { unfold grow_vB, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10'.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW1; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      - apply (chunk_ok_val SEGS E2 _ v 40 8 (SOff 36 0) n); [apply DV2; [lia | exact E36 | lia] | exact Hn | lia | exact Vn1].
      - apply (chunk_ok_val SEGS E2 _ v 48 8 (SOff 37 0) cap); [apply DV2; [lia | exact E37 | lia] | exact Hcap | lia
          | exact Vc1]. }
    assert (RA1 : region_ok SEGS E2 (mrestrict (w_H W2) (ms_mem ms1)) grow_vA).
    { unfold grow_vA, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10'.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply HRW1; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      - apply (chunk_ok_val SEGS E2 _ v 0 4 (SOff 33 0) ty); [apply DV2; [lia | exact E33 | lia] | exact Hty | lia |].
        rewrite Z.add_0_r. exact Vty1.
      - apply (chunk_ok_val SEGS E2 _ v 24 8 (SOff 34 0) kids); [apply DV2; [lia | exact E34 | lia] | exact Hkids | lia
          | exact Vk1].
      - apply (chunk_ok_val SEGS E2 _ v 32 8 (SOff 35 0) keys); [apply DV2; [lia | exact E35 | lia] | exact Hkeys | lia
          | exact Vy1]. }
    norm_ss HS2.
    pose proof (st_ok_pi_add_region E2 _ _ grow_vB HS2 ltac:(vm_compute; reflexivity) RB1) as HS3.
    match type of HS3 with ?P -> _ => assert (HD : P); [|specialize (HS3 HD); clear HD] end.
    { apply all_disjoint_of_extents.
      lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
      unfold grow_vB. cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
      cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U2', ?U10', ?U241', ?U253'. repeat split; lia. }
    norm_ss HS3. clear HS2.
    pose proof (st_ok_pi_add_region E2 _ _ grow_vA HS3 ltac:(vm_compute; reflexivity) RA1) as HS4.
    match type of HS4 with ?P -> _ => assert (HD : P); [|specialize (HS4 HD); clear HD] end.
    { apply all_disjoint_of_extents.
      lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
      unfold grow_vA. cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
      cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U2', ?U10', ?U241', ?U253'. repeat split; lia. }
    norm_ss HS4. clear HS3.
    assert (SHOK4 : sh_ok SEGS grow_Bx grow_SH E2 (mrestrict (w_H W2) (ms_mem ms1))).
    { unfold sh_ok, grow_SH. apply Forall_cons; [|apply Forall_nil]. split.
      + unfold grow_Bx. cbn [she_m she_lo she_hi].
        rewrite !U_SOff, U32', U10', !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; lia).
        change (rd_of SEGS (mrestrict (w_H W2) (ms_mem ms1))) with (aview SEGS (w_H W2) (ms_mem ms1)). exact HRA1.
      + unfold app_apart, grow_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
        rewrite !U_SOff, U32', U10', !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; lia).
        apply Happ. lia. }
    clear SHOK0.
    (* ---- the kept relation at ms1 (the call's journal, then the stretch to beqz) ---- *)
    pose proof (cj_kept_of_journalR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (grow_OR v) HJ1) as KJ1.
    assert (HFP1in : forall a, inFP FP1 a -> inFP FP a).
    { intros a (r & Hr & Hra'). exists r. split; [subst FP; apply in_or_app; right; exact (HFP1s r Hr) | exact Hra']. }
    assert (KC : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_A) (spZ regs) (grow_OR v) FP ly S W mem md
                   ly2 S2 W2 mem2 md2).
    { eapply (cj_kept_transR (SK := SK) SEGS B PST ARx LAWS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf));
        [exact K4 | exact KJ1 | exact HAR | exact HARc0 | lia | lia | intros a Ha; left; exact Ha
        | intros a Ha; left; exact (HFP1in a Ha)]. }
    destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 mem2 md2 (ms_mem ms1) _
      (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
      ltac:(lia) FS KC (fun _ _ => eq_refl) (fun _ H => H) HAR HARr Hceil2 Hslo2 Hshi2 HFrR HGR
      ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat0)) as (K5 & F5 & G5).
    pose proof (proj1 HJ2) as HARr1.
    (* ---- the run: `sd a0, 24(s1)` (the kids store), v's shadow check, `lw ty`, to `bne ty, 6` ---- *)
    assert (HvlocJ : (exists b m, In (b, m) (ablocks B ly2 S2) /\ b <= v /\ v + 56 <= b + req_size m) \/
      (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly2 cid pos <= v /\
         v + 56 <= frame_addr ly2 cid pos + fs_frame_bytes cid) \/ (spZ regs <= v /\ v + 56 <= spZ regs + e)).
    { destruct Hvloc2 as [Hb | [(cid & pos & Hf & H1 & H2) | Hx]];
        [left; exact Hb | right; left; exists cid, pos; rewrite <- Efrs; exact (conj Hf (conj H1 H2))
        | right; right; exact Hx]. }
    paj_run_tok_x_inv (RUNP P PLAW) HS4 HJ2 SHOK4 HPM grow_Bspan.
    { apply grow_awr_ok_fr with (v := v) (FR := 80);
        [lia | exact FS | exact He0 | grow_wr U2' U10' | apply grow_FP_v | exact HvlocJ]. }
    lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms1)) _ |- _ => rename Hf into HFr5 end.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms1)) _ |- _ => rename Hg into HG5 end.
    destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 (ms_mem ms1) _ _ _
      (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
      ltac:(lia) FS K5 F5 G5 HAR HARr1 Hceil2 Hslo2 Hshi2 HFr5 HG5
      ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat1)) as (K6 & F6 & G6).
    (* the new block: live at the post state, below alloc_ceiling, apart from the node and from grow's frame *)
    assert (Hnewin : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly2 S2))
      by (apply (Permutation_in _ (Permutation_sym PAB2)); left; reflexivity).
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hnewin) as (_ & _ & Hnc & _).
    assert (Hrqn : 56 * cap2R cap + cf_head <= req_size (56 * cap2R cap + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (56 * cap2R cap + cf_head) 0); lia).
    assert (Hcc : cap <= cap2R cap) by (unfold cap2R; destruct (Z.eqb_spec cap 0); lia).
    assert (HNEWW : forall a, res <= a < res + 56 * cap2R cap -> 0 <= a < 2 ^ 64 /\ ~ grow_wr 80 (spZ regs) v a).
    { intros a Ha. split; [lia|]. unfold grow_wr. intros Hw.
      assert (Hnv : ~ (v <= a < v + 56)) by (apply HAPn; lia).
      destruct Hw as [Hw | [Hw | Hw]]; lia. }
    assert (HMMB : cap2R cap <= 2 ^ 54) by (pose proof YG08cf.cf_malloc_max_bound; lia).
    assert (Hres64 : 0 <= res < 2 ^ 64) by lia.
    assert (D44 : sv_denot E2 (SOff 44 0) = Z_to_bv 64 res).
    { cbn [sv_denot]. rewrite E44, H10r. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity. }
    assert (Hlsum : Ledger.lsum Lam = 56 * cap + Ledger.lsum Lr).
    { rewrite (grow_lsum_perm _ _ PLam), grow_lsum_app, grow_lsum_kids by lia. reflexivity. }
    (* THE KIDS CALL'S EVENT (outcomes [true]): the live requests after it are the entry's moved by prhPg_ev 56 cap
       (PwGrowLive.grow_live_kids, from COM's blocks), and the leaf's post-implication moves any position at S by it *)
    assert (Hr2ne : getr regs2 10 <> w64 0).
    { rewrite H10r. intros Hq. apply Hresne. unfold w64 in Hq. apply (f_equal bv_unsigned) in Hq.
      rewrite !unsigned_lit_small in Hq by lia. exact Hq. }
    assert (HLV2 : Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
      (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) [prhPg_ev 56 cap]))
      by exact (grow_live_kids B ly S ly2 S2 kids cap res blr PAB1 PAB2).
    assert (HPOSK : forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i [prhPg_ev 56 cap] ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + 1)%nat H0 hist' S2).
    { intros sm x os i H0 hist Hpos Hrun. revert Hrun. unfold prhPg_ev.
      destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; intros Hrun.
      - exact (POSM Hresne (proj1 (Hcap0 Hc0)) sm x os i H0 hist Hpos Hrun).
      - exact (POSR Hresne (Hkids0' Hc0) sm x os i H0 hist Hpos Hrun). }
    psrr_branch_tok RUN BR HS4 SHOK4 grow_Bspan.
    * (* ty <> 6: store cap' at v + 48, return 0: grow's arm 4 (an array whose kids moved) *)
      assert (Hty6 : ty <> 6).
      { intros H6. rewrite H6 in E33.
        lazymatch goal with Hb : branch_taken _ _ _ = true |- _ =>
          cbn [sv_denot] in Hb; rewrite AG2 in Hb by lia; rewrite E33 in Hb; vm_compute in Hb; discriminate Hb end. }
      pose proof (proj1 HJ2) as HARr2.
      paj_run_tok_x_inv (RUNP P PLAW) HS4 HJ2 SHOK4 HPM grow_Bspan.
      { apply grow_awr_ok_fr with (v := v) (FR := 80);
          [lia | exact FS | exact He0 | grow_wr U2' U10' | apply grow_FP_v | exact HvlocJ]. }
      lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms2)) _ |- _ => rename Hf into HFr7 end.
      lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms2)) _ |- _ => rename Hg into HG7 end.
      destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 (ms_mem ms2) _ _ _
        (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
        ltac:(lia) FS K6 F6 G6 HAR HARr2 Hceil2 Hslo2 Hshi2 HFr7 HG7
        ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat2)) as (K7 & F7 & G7).
      unfold fpostWmR, fpostWR.
      eapply (grow_ret B ARx SK LAWS PL_grow (@STK_grow prh_img_A) W2 E2 _ _ _ e FP regs (grow_extra ty kids keys n cap)
        ly S Hp W mem md (grow_OR v) FP ly2 S2 Hp2 _ _ ltac:(lia) HS4 eq_refl ltac:(vm_compute; reflexivity));
        [ split; [intros nn Hnn; rewrite ?AG2 by lia; subst E; rewrite ?Eimg_low by (unfold A_TEXT; lia); reflexivity
                 | subst E2 E; reflexivity]
        | vm_compute; reflexivity
        | reflexivity
        | exact Hra
        | exact HJ2
        | exact K7
        | intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]
        | ].
      intros mat'. unfold fQmn. split; [|exact (PEND _ HPM)]. unfold gr_Q, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7. cbv beta.
      prreg HS4 (10%bv : bv 5) R10f.
      lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := ms_mem msF) in * end.
      pose proof (st_ok_region_nth SEGS E2 _ _ 0 _ HS4 ltac:(vm_compute; reflexivity)) as RAF.
      pose proof (st_ok_region_nth SEGS E2 _ _ 1 _ HS4 ltac:(vm_compute; reflexivity)) as RBF.
      cbn [ms_mem restrict] in RAF, RBF.
      assert (Rk : rd_u64 SEGS (mrestrict (w_H W2) mF) (v + 24) res).
      { split; [exact Hres64|].
        exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 24 8%N (SOff 44 0) res RAF U10' ltac:(cbn; tauto) D44
                 Hres64 ltac:(cbn; lia)). }
      assert (Ry : rd_u64 SEGS (mrestrict (w_H W2) mF) (v + 32) keys).
      { split; [exact Hkeys|].
        exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 32 8%N (SOff 35 0) keys RAF U10' ltac:(cbn; tauto)
                 (DV2 35%nat keys ltac:(lia) E35 Hkeys) Hkeys ltac:(cbn; lia)). }
      assert (Hc64 : 0 <= cap2R cap < 2 ^ 64) by lia.
      assert (Rc : rd_u64 SEGS (mrestrict (w_H W2) mF) (v + 48) (cap2R cap)).
      { split; [exact Hc64|].
        exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 48 8%N (SOff 38 0) (cap2R cap) RBF U10' ltac:(cbn; tauto)
                 (DV2 38%nat (cap2R cap) ltac:(lia) E38 Hc64) Hc64 ltac:(cbn; lia)). }
      assert (HSHK : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
                       aview SEGS (w_H W2) mF s = aview SEGS (w_H W2) mem2 s).
      { intros s Hs. apply aview_eq_of. apply F7. rewrite unsigned_lit_small by (unfold SHADOW_OFF in Hs; lia).
        unfold grow_wr. intros [Hw | [Hw | Hw]]; [unfold SHADOW_OFF in Hs; lia | |];
          exact (Happ s ltac:(lia) Hs). }
      split; [exact HROOM2|].
      split; [rewrite Heq; exact (grow_hull_one S S2 (ty =? 6) cap HHUk1)|].
      split.
      { rewrite Heq, grow_held_eq by lia. rewrite (proj2 (Z.eqb_neq ty 6) Hty6). lia. }
      right; right; right; left.
      split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|].
      split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
      exists res, ((res, 56 * cap2R cap) :: Lr).
      split; [exact Hr16|]. split; [exact Hrm|].
      split.
      { split; [exists blr; split; [exact PAB1 | exact PAB2]|].
        split; [exists hlr; split; [exact PHP | rewrite EHp2; apply Permutation_refl]|].
        exists Lr. split; [exact PLam | apply Permutation_refl]. }
      split.
      { eapply prh_ledger_keep; [exact HL2|]. intros a Hca.
        destruct (grow_cell_apart B ARx LAWS pst_img 80 ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v a
          ltac:(lia) HAR2 HL2 HAT2 Hsp128 Hoff Hca) as (Ha64 & Hnw).
        apply F7. rewrite unsigned_lit_small by lia. exact Hnw. }
      split.
      { rewrite Heq, grow_held_only by lia. rewrite (proj2 (Z.eqb_neq ty 6) Hty6). cbn [Ledger.lsum]. lia. }
      split.
      { apply (grow_bytes_keep W2 mem2 mF (spZ regs) v res kb HB2 F7); [lia | lia |].
        intros a Ha. exact (proj2 (HNEWW a ltac:(lia))). }
      split.
      { destruct HVIS2 as (HRAn & HVn).
        exact (vis_keep _ _ res (56 * cap2R cap) HSHK ltac:(lia) ltac:(lia) HRAn HVn). }
      split.
      { exact (grow_hdr_keep 80 (w_H W2) mem2 mF (spZ regs) v ty num str kids keys n cap res keys (cap2R cap)
                 HDR2 F7 G7 Hvstk Hv0' Hv64 Rk Ry Rc). }
      split.
      { unfold pj_slots_atR, prh_lin.
        split; [exact Hty56|]. split; [lia|]. split; [intros Hz; lia|].
        intros _. split; [left; reflexivity | intros H6; contradiction]. }
      (* outcomes [true]: E = the kids realloc's event; the live requests and the position move by it *)
      rewrite (proj2 (Z.eqb_neq ty 6) Hty6), Heq, grow_evs_true.
      split; [exact HLV2 | exact HPOSK].
    * (* ty = 6: the keys call (A 0x86ab8): a0 = keys (chunk 32), a1 = s3 = 8 cap', ra the return site, s0 = v + 48 *)
      assert (Hty6 : ty = 6).
      { destruct Hty56 as [H5 | H6]; [exfalso | exact H6]. rewrite H5 in E33.
        lazymatch goal with Hb : branch_taken _ _ _ = false |- _ =>
          cbn [sv_denot] in Hb; rewrite AG2 in Hb by lia; rewrite E33 in Hb; vm_compute in Hb; discriminate Hb end. }
      pose proof (proj1 HJ2) as HARr2.
      paj_run_tok_x_inv (RUNP P PLAW) HS4 HJ2 SHOK4 HPM grow_Bspan.
      { apply grow_awr_ok_fr with (v := v) (FR := 80);
          [lia | exact FS | exact He0 | grow_wr U2' U10' | apply grow_FP_v | exact HvlocJ]. }
      lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W2) (ms_mem ms2)) _ |- _ => rename Hf into HFr7 end.
      lazymatch goal with Hg : mem_grows (mrestrict (w_H W2) (ms_mem ms2)) _ |- _ => rename Hg into HG7 end.
      destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E2 _ W2 mem2 (ms_mem ms2) _ _ _
        (spZ regs) v FP ly S Hp W mem md ly2 S2 Hp2
        ltac:(lia) FS K6 F6 G6 HAR HARr2 Hceil2 Hslo2 Hshi2 HFr7 HG7
        ltac:(grow_wr_tac U2' U10') (same_but_materialized_wvb_any _ mat2)) as (K7 & F7 & G7).
      (* the call's register facts *)
      prreg HS4 (2%bv : bv 5) R2k. prreg HS4 (1%bv : bv 5) R1k. prreg HS4 (3%bv : bv 5) R3k.
      prreg HS4 (4%bv : bv 5) R4k. prreg HS4 (10%bv : bv 5) R10k. prreg HS4 (8%bv : bv 5) R8k.
      pose proof (st_ok_restrict_reg SEGS (w_H W2) E2 _ ms3 (11%bv : bv 5) HS4) as R11k.
      change (sr_get _ (11%bv : bv 5)) with (SAlu ALU_SLL (SOff 38 0) (SLit 3)) in R11k.
      assert (E38' : ew E2 38 = Z_to_bv 64 (cap2R cap)) by (rewrite AG2 by lia; exact E38).
      assert (Hsp3 : spZ (ms_regs ms3) = spZ regs + e + (-80 - e)).
      { unfold spZ at 1. rewrite R2k, U2'. rewrite unsigned_lit_small by lia. lia. }
      assert (H10k : getr (ms_regs ms3) 10 = w64 keys) by (rewrite R10k, AG2 by lia; rewrite E35; reflexivity).
      assert (H11k : getr (ms_regs ms3) 11 = w64 (8 * cap2R cap)).
      { rewrite R11k, denot_lit_U. unfold w64. f_equal.
        rewrite U_SAlu, U_SLit, (U_atom E2 38 (cap2R cap) E38') by lia.
        cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
        unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
      assert (H8k : s0Z (ms_regs ms3) = v + 48).
      { unfold s0Z. rewrite R8k, U10'. rewrite unsigned_lit_small by lia. reflexivity. }
      (* the node's keys and cap fields at the call state, and at the kids call's post state *)
      pose proof (st_ok_region_nth SEGS E2 _ _ 0 _ HS4 ltac:(vm_compute; reflexivity)) as RAk.
      pose proof (st_ok_region_nth SEGS E2 _ _ 1 _ HS4 ltac:(vm_compute; reflexivity)) as RBk.
      cbn [ms_mem restrict] in RAk, RBk.
      assert (Vy3 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (v + 32) (N.to_nat 8) keys)
        by exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 32 8%N (SOff 35 0) keys RAk U10' ltac:(cbn; tauto)
                    (DV2 35%nat keys ltac:(lia) E35 Hkeys) Hkeys ltac:(cbn; lia)).
      assert (Vc3 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms3)) (v + 48) (N.to_nat 8) cap)
        by exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 48 8%N (SOff 37 0) cap RBk U10' ltac:(cbn; tauto)
                    (DV2 37%nat cap ltac:(lia) E37 Hcap) Hcap ltac:(cbn; lia)).
      pose proof HDR2 as (_ & _ & _ & _ & _ & (_ & Vy2) & _ & (_ & Vc2)).
      pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ElyT & _).
      (* the chain at v + 48 at the keys call: the kids call's, through the call (the node's bytes kept, the rest above
         sp kept by the callee's journal) and grow's own stores (below v + 32 or in v's unwritten fields) *)
      assert (HCH3 : exists ch3, achain ly2 (aview SEGS (w_H W2) (ms_mem ms3)) (spZ regs - 80) (v + 48) ch3).
      { destruct (Z_lt_ge_dec (v + 48) YM05.alloc_ceiling) as [Hlo48 | Hhi48].
        { exists []. apply achain_low. exact Hlo48. }
        assert (Hvsp : spZ regs <= v).
        { destruct Hvloc as [(b & m & Hinb & H1 & H2) | [(cid & pos & Hinf & H1 & H2) | H]].
          - destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hinb) as (_ & _ & Hbc & _).
            assert (Hqm : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
          - destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hfr).
            pose proof (proj1 (Forall_forall _ _) Hfr (cid, pos) Hinf) as (_ & Hfc). cbn [fst snd] in Hfc. lia.
          - lia. }
        exists ch1. apply (achain_ly_top ly ly2); [exact ElyT|].
        refine (achain_kept_hi _ _ _ _ _ _ Hch1 ltac:(lia) _).
        intros a Ha Hb. transitivity (aview SEGS (w_H W2) mem2 a).
        - destruct (Z_lt_ge_dec a (v + 40)) as [A1 | A1].
          { exact (aview_of_val_mem_eq (w_H W2) mem2 (ms_mem ms3) (v + 32) keys Vy2 Vy3 a ltac:(lia)). }
          destruct (Z_lt_ge_dec a (v + 48)) as [A2 | A2].
          { apply aview_eq_of. apply F7. rewrite unsigned_lit_small by lia. unfold grow_wr. lia. }
          destruct (Z_lt_ge_dec a (v + 56)) as [A3 | A3].
          { exact (aview_of_val_mem_eq (w_H W2) mem2 (ms_mem ms3) (v + 48) cap Vc2 Vc3 a ltac:(lia)). }
          apply aview_eq_of. apply F7. rewrite unsigned_lit_small by lia. unfold grow_wr. lia.
        - destruct (Z_lt_ge_dec a (v + 56)) as [A1 | A1]; [exact (proj1 (GVK a ltac:(lia))) |].
          apply G1c; lia. }
      destruct HCH3 as (ch3 & Hch3).
      (* the callee's premises at the call state *)
      assert (HROk : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) (ms_mem ms3))).
      { intros a Hro Ho He.
        assert (Himg : in_img SEGS a)
          by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img a Hr)]).
        pose proof (pa_segs_low a Himg) as Hlow. unfold kLowMemEnd in Hlow.
        pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F11 & _).
        rewrite <- (HROc a Hro Ho He).
        transitivity (aview SEGS (w_H W2) mem2 a).
        - apply aview_eq_of. apply F7. rewrite unsigned_lit_small by lia. unfold grow_wr.
          intros [Hw | [Hw | Hw]]; [lia | exact (Hoff a ltac:(lia) Himg) | exact (Hoff a ltac:(lia) Himg)].
        - apply F11; [exact Himg | exact Ho | exact He | exact (ro_not_pst a Hro) |].
          apply fp_spares_closed. intros (r & Hr & H0). subst FP1.
          destruct (Z.eqb_spec kids 0) as [Hk0 | Hk0]; [destruct Hr|].
          unfold ablocks_fp in Hr. cbn [map In fst snd] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in H0.
          assert (Hcp : 0 < cap)
            by (destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [exfalso; exact (Hk0 (proj1 (Hcap0 Hc0))) | lia]).
          destruct (Hcapp Hcp) as (Hink & _). pose proof HLED as (_ & _ & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hink) as (_ & Hbk & _). cbn [fst snd] in Hbk.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & Hb4096 & _). lia. }
      assert (HL2c : prh_ledger B ly2 S2 Hp2 W2 (ms_mem ms3) ((res, 56 * cap2R cap) :: Lr)
                       (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (cnt + 1) fail ran most own).
      { eapply prh_ledger_keep; [exact HL2|]. intros a Hca.
        destruct (grow_cell_apart B ARx LAWS pst_img 80 ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ _ _ _ regs e v a
          ltac:(lia) HAR2 HL2 HAT2 Hsp128 Hoff Hca) as (Ha64 & Hnw).
        apply F7. rewrite unsigned_lit_small by lia. exact Hnw. }
      set (oldy := if cap =? 0 then [] else yb).
      assert (Hyb_len : Z.of_nat (length yb) = 8 * cap) by exact (proj2 (proj2 (proj2 (HOLD Heq)) Hty6)).
      assert (HOLDk : keys = 0 /\ 8 * cap = 0 /\ oldy = [] \/
                      In (keys, 8 * cap) ((res, 56 * cap2R cap) :: Lr) /\ bytes_at W2 (ms_mem ms3) keys oldy /\
                      Z.of_nat (length oldy) = 8 * cap).
      { subst oldy. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
        - left. split; [exact (proj2 (Hcap0 Hc0) Hty6)|]. split; [lia | reflexivity].
        - right. assert (Hcp : 0 < cap) by lia. destruct (Hcapp Hcp) as (Hink & Hky). specialize (Hky Hty6).
          unfold prh_lin in Hink, Hky.
          assert (Hky2 : In (keys, 8 * cap) Lr).
          { apply (Permutation_in _ PLam) in Hky. unfold kids_blkR in Hky. rewrite (proj2 (Z.eqb_neq cap 0) Hc0) in Hky.
            destruct Hky as [Hq | Hky]; [injection Hq as Ek Ekk; lia | exact Hky]. }
          split; [right; exact Hky2|]. split; [|exact Hyb_len].
          destruct (HOLD Heq) as (_ & _ & HY). destruct (HY Hty6) as (Hyb & _).
          pose proof HLED as (_ & HND & HFl & _).
          pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hbk & _). cbn [fst snd] in Hk, Hbk.
          pose proof (proj1 (Forall_forall _ _) HFl (kids, 56 * cap) Hink) as (Hk' & Hbkid & _). cbn [fst snd] in Hk', Hbkid.
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & Hb4096 & Hbc & _).
          destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbkid) as (_ & Hb4096' & Hbc' & _).
          assert (Hrqk : 8 * cap + cf_head <= req_size (8 * cap + cf_head))
            by (unfold req_size; destruct (Z.eqb_spec (8 * cap + cf_head) 0); lia).
          assert (Hrqd : 56 * cap + cf_head <= req_size (56 * cap + cf_head))
            by (unfold req_size; destruct (Z.eqb_spec (56 * cap + cf_head) 0); lia).
          assert (Hne : (keys - cf_head, 8 * cap + cf_head) <> (kids - cf_head, 56 * cap + cf_head))
            by (intros Heqb; injection Heqb; intros; lia).
          pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md _ _ _ _ HAR Hbk Hbkid Hne) as Hdis.
          unfold zdisjoint in Hdis. cbn [fst snd] in Hdis.
          assert (Hin2' : In (keys - cf_head, keys - cf_head + req_size (8 * cap + cf_head))
                            (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
          { unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), (proj2 (Z.eqb_eq ty 6) Hty6).
            cbn [orb negb app]. unfold prhReader_ab, ablocks_fp. cbn [map fst snd]. right; left; reflexivity. }
          assert (HNWk : forall a, keys <= a < keys + 8 * cap -> ~ grow_wr 80 (spZ regs) v a).
          { intros a Ha.
            destruct (grow_slot_apart B ARx LAWS 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap
              _ _ a ltac:(lia) ltac:(lia) HAR HLED HAT Hsp128 HSLOT HAP Hin2') as (_ & Hnw); [lia | exact Hnw]. }
          assert (Hyc : bytes_at W (ms_mem ms0) keys yb).
          { apply (grow_bytes_keep W mem (ms_mem ms0) (spZ regs) v keys yb Hyb F4); [lia | lia |].
            intros a Ha. apply HNWk. lia. }
          assert (Hbk2 : In (keys - cf_head, 8 * cap + cf_head) (ablocks B ly2 S2)).
          { pose proof HL2 as (_ & _ & HFl2 & _).
            exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFl2 (keys, 8 * cap) (or_intror Hky2)))). }
          assert (Hy2 : bytes_at W2 mem2 keys yb).
          { apply (bytes_at_aview W W2 (ms_mem ms0) mem2 keys yb Hyc). intros a Ha.
            pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2c & _).
            replace a with ((keys - cf_head) + (a - (keys - cf_head))) by lia.
            apply (G2c _ _ _ Hbk Hbk2); [clear - Ha Hyb_len Hrqk Hhd0; lia|].
            intros ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi. subst FP1.
            rewrite (proj2 (Z.eqb_neq kids 0)) in Hr by lia. unfold ablocks_fp in Hr. cbn [map fst snd In] in Hr.
            destruct Hr as [Hr | []]. injection Hr as <- <-. destruct Hdis as [Hdis | Hdis]; dlia. }
          apply (grow_bytes_keep W2 mem2 (ms_mem ms3) (spZ regs) v keys yb Hy2 F7); [lia | lia |].
          intros a Ha. apply HNWk. lia. }
      (* the keys realloc's live premise: event 1 of the text's live room at each event, at S2, whose live list is the
         entry's moved by the kids event (HLV2; PwGrowLive.grow_room_keys) *)
      assert (HLIVEk : cnt + 1 <> fail -> blocks_bytes S2 + (8 * cap2R cap + cf_head) <= LIVE_MAX).
      { intros _. destruct (HLIVE Heq) as (_ & Hl). rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6) in Hl.
        exact (grow_room_keys B ly2 S S2 cap Hl HLV2). }
      (* the keys call's live counts (tfuzz_realloc_specX's premises at S2): the text's peak premises along the
         all-granted events [kids; keys] bound the count after the kids event, and S2's live requests are the entry's
         moved by that event (HLV2), so PwGrowG.grow_cnt_at at j = 1 gives them; no position and no agreement is needed *)
      assert (HEVS6 : prhPg_evs (ty =? 6) n cap [] = [prhPg_ev 56 cap; prhPg_ev 8 cap])
        by (rewrite (proj2 (Z.eqb_eq ty 6) Hty6), Heq, grow_evs_all; reflexivity).
      assert (HSEC2 : YGcfRoomLive.sec_cnt S2 <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
      { rewrite grow_sec_cnt. unfold gr_pk_sec in HPKS. rewrite HEVS6 in HPKS. exact (grow_cnt_at _ S S2 [prhPg_ev 56 cap; prhPg_ev 8 cap] 1 _ HLV2 HPKS). }
      assert (HC242 : YGcfRoomLive.ccnt24 S2 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
      { rewrite grow_ccnt24. unfold gr_pk_24 in HPK24. rewrite HEVS6 in HPK24. exact (grow_cnt_at _ S S2 [prhPg_ev 56 cap; prhPg_ev 8 cap] 1 _ HLV2 HPK24). }
      set (FP1k := if keys =? 0 then [] else ablocks_fp [(keys - cf_head, 8 * cap + cf_head)]).
      assert (Hra3 : raZ (ms_regs ms3) < YM05.alloc_ceiling).
      { unfold raZ. rewrite R1k. pose proof grow_keys_ret_ceil as Hslotc.
        match goal with |- bv_unsigned ?r < _ =>
          replace (bv_unsigned r) with (BASE + (GROW_OFF + 256)) by (vm_compute; reflexivity) end.
        exact Hslotc. }
      (* THE HULL: the keys call's budget is grow's less the kids call's use (the second event of the list) *)
      assert (HKCy : keys = 0 <-> cap = 0).
      { split; [|intros Hcz; exact (proj2 (Hcap0 Hcz) Hty6)].
        intros Hky0. destruct (Z.eq_dec cap 0) as [Hcz | Hcz]; [exact Hcz|]. exfalso.
        assert (Hcpy : 0 < cap) by flia. destruct (Hcapp Hcpy) as (_ & Hkyy). specialize (Hkyy Hty6). unfold prh_lin in Hkyy.
        pose proof HLED as (_ & _ & HFly & _).
        pose proof (proj1 (Forall_forall _ _) HFly (keys, 8 * cap) Hkyy) as (Hky1 & Hby1 & _). cbn [fst snd] in Hky1, Hby1.
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hby1) as (_ & Hby4096 & _). flia. }
      assert (HHUy : PresetHullBudget.hull_budget S2
        (if keys =? 0 then [PresetReqAt.HMal (8 * cap2R cap + cf_head)]
         else [PresetReqAt.HRe (8 * cap + cf_head) (8 * cap2R cap + cf_head)])).
      { rewrite (grow_hull_ev keys 8 cap HKCy). apply (grow_hull_keys S S2 cap); [|exact HHUk1].
        rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6) in HHULL. exact HHULL. }
      eapply (SRr'_bind SEGS RZ_cf).
      { eapply (@aj_call_xW_spR fx rc SK SEGS B PST ARx _ LAWS (@pa_segs_low _ _ PI_prog_A) (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
      W2 E2 _ ms3
          (STK_grow + e) (spZ regs + e) FP ly S Hp W mem md [] ly2 S2 Hp2 _ _
          (@STK_fuzz_realloc prh_img_A) 0 FP1k (-80 - e) _ ch3
          (fQmn (ms_mem ms3) (gr_KR ly2 S2 Hp2 W2 keys (8 * cap)
             (8 * cap2R cap) oldy ((res, 56 * cap2R cap) :: Lr)
             (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (cnt + 1) fail ran most own)) HS4 eq_refl HJ2).
        - exact Hsp3.
        - rewrite Zminus_mod, He16. reflexivity.
        - lia.
        - exact HSTK1.
        - lia.
        - lia.
        - reflexivity.
        - lia.
        - rewrite R3k, AG2 by lia. rewrite E3. exact Hgp.
        - rewrite R4k, AG2 by lia. rewrite E4. exact Htp.
        - exact R1k.
        - apply ret_ok_even. vm_compute. reflexivity.
        - apply Z.leb_le. vm_compute. reflexivity.
        - rewrite H8k. replace (spZ regs + e + (-80 - e)) with (spZ regs - 80) by lia. exact Hch3.
        - intros Hpre Hwin.
          assert (HTOPk : spZ (ms_regs ms3) + 64 <= ly_stk_hi ly2) by (rewrite Hsp3, Ehi2; lia).
          assert (Hn0k : 0 <= 8 * cap2R cap) by lia.
          assert (Hnmaxk : 8 * cap2R cap + cf_head < cf_malloc_max) by lia.
          eapply (SRr'_mono SEGS RZ_cf).
          { exact (HREALLOC ly2 S2 Hp2 W2 (ms_regs ms3) (ms_mem ms3) _ ch3
              keys (8 * cap) (8 * cap2R cap) oldy
              ((res, 56 * cap2R cap) :: Lr) (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (cnt + 1) fail ran most own
              (conj Hpre (conj HROk (conj HTOPk (conj Hra3 HFRM0)))) HROOM2 HUNIVm HSEC2 HC242 HHUy HU1 HU2 H10k H11k Hn0k
              Hnmaxk
              HL2c HOLDk HLIVEk). }
          intros W' c' _ Hq. apply fpostW_x_of_apostR. exact Hq.
        - intros a Ha. left. subst FP1k. destruct (Z.eqb_spec keys 0) as [Hk0 | Hk0].
          + destruct Ha as (r & Hr & _). destruct Hr.
          + assert (Hck : cap <> 0) by (intros Hz; apply Hk0; exact (proj2 (Hcap0 Hz) Hty6)).
            destruct Ha as (r & Hr & Hrin). exists r. split; [|exact Hrin]. subst FP. apply in_or_app. right.
            unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hck), (proj2 (Z.eqb_eq ty 6) Hty6).
            unfold prhReader_ab, ablocks_fp in Hr |- *. cbn [orb negb app map fst snd] in Hr |- *. destruct Hr as [<- | []].
            right; left. reflexivity. }
      cbv beta. intros W3 c3 Hle3 (ly3 & S3 & Hp3 & regs3 & mem3 & md3 & k3 & Hc3 & HJ3 & HJ1k & HXk & HPk & HK3).
      subst c3.
      unfold fQmn in HK3. destruct HK3 as (HK3 & HMN3).
      pose proof (PCALL _ _ HMN3 HPM) as HPM3. clear HPM HMN3. rename HPM3 into HPM.
      (* ---- THE KEYS CALL'S RETURN SITE (A 0x86abc): re-seat, the frame / GOT / cell kept ---- *)
      pose proof (proj1 HJ2) as HARc2.
      pose proof HJ3 as (HAR3 & _ & _ & HWLE3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
      pose proof HJ1k as (_ & _ & _ & _ & _ & HFRS1k & _ & _ & G1k & _).
      destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARc2) as (Kcellk & _ & Kgotk & _).
      destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR3) as (Kcell3 & _ & Kgot3 & _).
      rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgotk, Kgot3. rewrite (pal_cell B TL) in Kcellk, Kcell3.
      jafter_call_keep_pi HS4 56%nat regs3 (mrestrict (w_H W3) mem3) HPk [2; 3; 4]%nat HS5.
      match type of HS5 with ?Q -> _ =>
        let HQ := fresh "HQ" in
        assert (HQ : Q); [| specialize (HS5 HQ); clear HQ] end.
      { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
        - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2'; intros a Ha.
          + apply (mbyte_of_aview SEGS). apply G1k; flia.
          + intros _. apply (apresent_writable SEGS). apply HPR3. flia.
        - apply (region_kept_val_at E2 _ _ 241 (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 12))); [exact U241' | | | flia].
          + exact (val_mem_of_rdword SEGS _ _ _ _ Kgotk).
          + exact (val_mem_of_rdword SEGS _ _ _ _ Kgot3).
        - apply (region_kept_val_at E2 _ _ 253 (VAL (A_OBJ 12)) 8 SHADOW_OFF); [exact U253' | | | flia].
          + exact (val_mem_of_rdword SEGS _ _ _ _ Kcellk).
          + exact (val_mem_of_rdword SEGS _ _ _ _ Kcell3). }
      rewrite <- restrict_mkst_fx in HS5.
      remember (havoc E2 56 (map (getr regs3) CLOB)) as Ek3 eqn:HEk3 in HS5.
      assert (HEIk3 : img_env VAL A_LIM Ek3).
      { subst Ek3. apply img_env_havoc; [exact HEI2|]. rewrite length_map. apply Nat.leb_le. reflexivity. }
      assert (AG3 : forall nn, (nn < 56)%nat -> ew Ek3 nn = ew E2 nn) by (intros nn Hnn; subst Ek3; apply ew_havoc_old; flia).
      assert (U2'' : bv_unsigned (ew Ek3 2) = spZ regs) by (rewrite AG3 by flia; exact U2').
      assert (U10'' : bv_unsigned (ew Ek3 10) = v) by (rewrite AG3 by flia; exact U10').
      assert (SHOK5 : sh_ok SEGS grow_Bx [] Ek3 (mrestrict (w_H W3) mem3)) by constructor.
      pose proof (proj1 HJ3) as HARr3.
      (* ---- what the keys call leaves of the node, the new kids block and the layout ---- *)
      pose proof HJ3 as (_ & Hly3 & _).
      pose proof Hly3 as (_ & _ & _ & _ & _ & ElyF3 & _ & _ & _ & Elo3 & Ehi3 & _).
      assert (Hceil3 : YM05.alloc_ceiling <= ly_stk_lo ly3) by (rewrite Elo3; exact Hceil).
      assert (Hslo3 : ly_stk_lo ly3 + @STK_grow prh_img_A <= spZ regs) by (rewrite Elo3; flia).
      assert (Hshi3 : spZ regs <= ly_stk_hi ly3) by (rewrite Ehi3; flia).
      assert (Efrs3 : frames S3 = frames S2) by (rewrite HFRS1k; reflexivity).
      assert (Efa3 : forall cid pos, frame_addr ly3 cid pos = frame_addr ly2 cid pos)
        by (intros cid pos; unfold frame_addr; rewrite ElyF3, ElyF; reflexivity).
      assert (Hoy0 : keys = 0 -> oldy = []).
      { intros Hk0. subst oldy. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [reflexivity | exfalso].
        assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6). unfold prh_lin in Hky.
        pose proof HLED as (_ & _ & HFl & _).
        pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (_ & Hbk & _). cbn [fst snd] in Hbk.
        destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & Hb4096 & _). flia. }
      assert (HnFk : forall a, v <= a < v + 56 -> ~ inFP FP1k a).
      { intros a Ha ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi. subst FP1k.
        destruct (Z.eqb_spec keys 0) as [Hk0 | Hk0]; [destruct Hr|].
        assert (Hck : cap <> 0) by (intros Hz; apply Hk0; exact (proj2 (Hcap0 Hz) Hty6)).
        assert (Hin2' : In (lo, hi) (ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap)))).
        { unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hck), (proj2 (Z.eqb_eq ty 6) Hty6).
          unfold prhReader_ab, ablocks_fp in Hr |- *. cbn [orb negb app map fst snd] in Hr |- *. right. exact Hr. }
        exact (grow_slot_v B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi a
                 ltac:(flia) HAR HLED HAT Hsp128 HSLOT HAP Hin2' ltac:(flia) Ha). }
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc2 & _).
      assert (Hpc2 : forall a, spZ regs <= a < spZ regs + e -> apresent (w_H W2) (ms_mem ms3) a)
        by (intros a Ha; apply HPRc2; flia).
      assert (GVK3 : forall a, v <= a < v + 56 ->
        aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) (ms_mem ms3) a /\ apresent (w_H W3) mem3 a)
        by exact (grow_v_kept_nf ly2 S2 Hp2 W2 (ms_mem ms3) _ _ _ _ _ _ _ _ regs e v _ _ FP1k ly3 S3 Hp3 W3 mem3 md3 k3
                    HARc2 HL2c HAT2 Hsp128 Hv4096 Hv64 Hoff Hpc2 HJ1k ltac:(flia) HnFk).
      assert (Rk3 : rd_u64 SEGS (mrestrict (w_H W2) (ms_mem ms3)) (v + 24) res).
      { split; [exact Hres64|].
        exact (field_of_region SEGS E2 _ 10 v _ _ _ _ _ 24 8%N (SOff 44 0) res RAk U10' ltac:(cbn; tauto) D44
                 Hres64 ltac:(cbn; flia)). }
      assert (HDR3 : pj_hdrR SEGS (mrestrict (w_H W2) (ms_mem ms3)) v ty num str res keys n cap)
        by exact (grow_hdr_keep 80 (w_H W2) mem2 (ms_mem ms3) (spZ regs) v ty num str kids keys n cap res keys cap
                    HDR2 F7 G7 Hvstk Hv0' Hv64 Rk3 (conj Hkeys Vy3) (conj Hcap Vc3)).
      assert (HDR3' : pj_hdrR SEGS (mrestrict (w_H W3) mem3) v ty num str res keys n cap)
        by exact (pj_hdr_aview (w_H W2) (w_H W3) (ms_mem ms3) mem3 v ty num str res keys n cap HDR3 GVK3).
      (* the new kids block is apart from the keys call's footprint, so it is live after the call with its bytes *)
      assert (HnFn : forall a, res - cf_head <= a < res - cf_head + req_size (56 * cap2R cap + cf_head) ->
                       ~ inFP FP1k a).
      { intros a Ha ((lo & hi) & Hr & Hlo & Hhi). cbn [fst snd] in Hlo, Hhi. subst FP1k.
        destruct (Z.eqb_spec keys 0) as [Hk0 | Hk0]; [destruct Hr|].
        unfold ablocks_fp in Hr. cbn [map In fst snd] in Hr. destruct Hr as [Hr | []]. injection Hr as <- <-.
        assert (Hck : cap <> 0) by (intros Hz; apply Hk0; exact (proj2 (Hcap0 Hz) Hty6)).
        assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6). unfold prh_lin in Hky.
        assert (Hky2 : In (keys, 8 * cap) Lr).
        { apply (Permutation_in _ PLam) in Hky. unfold kids_blkR in Hky. rewrite (proj2 (Z.eqb_neq cap 0) Hck) in Hky.
          destruct Hky as [Hq | Hky]; [injection Hq as Ek Ekk; flia | exact Hky]. }
        pose proof HL2 as (_ & _ & HFl2 & _).
        pose proof (proj1 (Forall_forall _ _) HFl2 (keys, 8 * cap) (or_intror Hky2)) as (_ & Hbk2 & _).
        cbn [fst snd] in Hbk2.
        assert (Hne : (res - cf_head, 56 * cap2R cap + cf_head) <> (keys - cf_head, 8 * cap + cf_head))
          by (intros Hq; injection Hq; intros; flia).
        pose proof (sep_blocks_x SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ _ _ HAR2 Hnewin Hbk2 Hne) as Hdis.
        unfold zdisjoint in Hdis. cbn [fst snd] in Hdis. destruct Hdis as [Hdis | Hdis]; dlia. }
      assert (Hnew3 : In (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly3 S3)).
      { pose proof HJ1k as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone3 & _).
        assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
        destruct (in_dec Hdec (res - cf_head, 56 * cap2R cap + cf_head) (ablocks B ly3 S3)) as [Hin3 | Hout]; [exact Hin3|].
        exfalso. apply (HnFn (res - cf_head + 0)); [flia|].
        exact (Hgone3 _ _ 0 Hnewin Hout ltac:(flia)). }
      assert (HB3 : bytes_at W3 mem3 res kb).
      { assert (HB2c : bytes_at W2 (ms_mem ms3) res kb).
        { apply (grow_bytes_keep W2 mem2 (ms_mem ms3) (spZ regs) v res kb HB2 F7); [flia | flia |].
          intros a Ha. exact (proj2 (HNEWW a ltac:(flia))). }
        apply (bytes_at_aview W2 W3 (ms_mem ms3) mem3 res kb HB2c). intros a Ha.
        pose proof HJ1k as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G2k & _).
        replace a with ((res - cf_head) + (a - (res - cf_head))) by flia.
        apply (G2k _ _ _ Hnewin Hnew3); [clear - Ha Hkb_len Hrqn Hcc Hhd0; lia|]. apply HnFn. lia. }
      (* the kept relation at the keys call's post state *)
      pose proof (cj_kept_of_journalR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (grow_OR v) HJ1k) as KJ1k.
      assert (HFP1kin : forall a, inFP FP1k a -> inFP FP a).
      { intros a (r & Hr & Hra'). exists r. split; [|exact Hra']. subst FP. apply in_or_app. right. subst FP1k.
        destruct (Z.eqb_spec keys 0) as [Hk0 | Hk0]; [destruct Hr|].
        assert (Hck : cap <> 0) by (intros Hz; apply Hk0; exact (proj2 (Hcap0 Hz) Hty6)).
        unfold kids_blkR, keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hck), (proj2 (Z.eqb_eq ty 6) Hty6).
        unfold prhReader_ab, ablocks_fp in Hr |- *. cbn [orb negb app map fst snd] in Hr |- *. destruct Hr as [<- | []].
        right; left. reflexivity. }
      assert (KCk : cj_keptR (SK := SK) SEGS B PST (wle' SEGS RZ_cf) (@STK_grow prh_img_A) (spZ regs) (grow_OR v) FP ly S W mem md
                      ly3 S3 W3 mem3 md3).
      { eapply (cj_kept_transR (SK := SK) SEGS B PST ARx LAWS (wle' SEGS RZ_cf) (wle'_trans SEGS RZ_cf));
          [exact K7 | exact KJ1k | exact HAR | exact HARc2 | flia | flia | intros a Ha; left; exact Ha
          | intros a Ha; left; exact (HFP1kin a Ha)]. }
      assert (E60 : ew Ek3 60 = getr regs3 10).
      { subst Ek3. change 60%nat with (56 + 4)%nat.
        rewrite (ew_havoc_new E2 56 (map (getr regs3) CLOB) 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; flia).
        reflexivity. }
      psrr_branch_tok RUN BR HS5 SHOK5 grow_Bspan.
      -- (* the keys realloc returned NULL: grow returns -1, its arms 5 (the chosen failure) and 6 (refused) *)
         lazymatch goal with Hb : branch_taken BC_EQ _ _ = true |- _ => rename Hb into Hres2 end.
         assert (Hres0k : bv_unsigned (getr regs3 10) = 0).
         { rewrite branch_eq_U in Hres2. apply Z.eqb_eq in Hres2. rewrite U_lit in Hres2 by flia.
           rewrite U_SOff, E60, Z.add_0_r in Hres2. unfold zcanon, M64 in Hres2. rewrite Z.mod_small in Hres2; [exact Hres2|].
           apply u64_range. }
         pose proof HK3 as HK3k.
         destruct HK3 as (res2 & H10r2 & HROOM3 & HHU2 & POS0y & POSMy & POSRy & OUTMy & OUTRy & ARMS2).
         assert (HHUy1 : PresetHullBudget.hull_used S2 S3 [prhPg_ev 8 cap])
           by (rewrite <- (grow_hull_ev keys 8 cap HKCy); exact HHU2).
         rewrite H10r2 in Hres0k. unfold w64 in Hres0k.
         (* the keys result is NULL on every arm this branch can take *)
         assert (HresNy : forall r', 4096 + cf_head <= r' -> In (r' - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3) ->
           r' = res2 -> False).
         { intros r' H4096 Hin3 Her. subst r'.
           destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hbc & _).
           assert (Hrq0 : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
             by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); flia).
           rewrite unsigned_lit_small in Hres0k by flia. flia. }
         assert (Hr0y : res2 = 0).
         { destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
           - assert (Hk0 : keys = 0) by exact (proj2 (Hcap0 Hc0) Hty6).
             destruct ARMS2 as [(_ & HAP0) | [(Hp0 & _) | [(Hp0 & _) | (Hp0 & _)]]]; [| flia | flia | flia].
             destruct HAP0 as [(_ & Hz & _) | [(_ & Hz & _) | (Hcf3 & Hrs & _ & _ & _ & Eab3 & _)]]; [exact Hz | exact Hz |].
             exfalso. exact (HresNy res2 Hrs ltac:(rewrite Eab3; apply in_or_app; right; left; reflexivity) eq_refl).
           - assert (Hkeys0 : keys <> 0).
             { assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
               unfold prh_lin in Hky. pose proof HLED as (_ & _ & HFl & _).
               pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
               destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). flia. }
             destruct ARMS2 as [(Hp0 & _) | [(_ & _ & Hz & _) | [(_ & _ & Hz & _) |
               (_ & _ & Hrs & _ & l1' & l2' & _ & _ & _ & (b1' & b2' & _ & _ & Hperm3) & _)]]];
               [exfalso; exact (Hkeys0 Hp0) | exact Hz | exact Hz |].
             exfalso. exact (HresNy res2 Hrs (Permutation_in _ (Permutation_sym Hperm3) (or_introl eq_refl)) eq_refl). }
         assert (Hcnt2 : (cnt + 1 + 1) mod 2 ^ 64 = cnt + 2) by (rewrite Z.mod_small; flia).
         assert (HNULL : ablocks B ly3 S3 = ablocks B ly2 S2 /\ Permutation Hp3 Hp2 /\ bytes_at W3 mem3 keys oldy /\
           ((cnt + 1 = fail /\ prh_ledger B ly3 S3 Hp3 W3 mem3 ((res, 56 * cap2R cap) :: Lr)
                (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (cnt + 2) SIZE_MAXZ ran most own) \/
            (cnt + 1 <> fail /\
             (exists S1, blocks S3 = blocks S1 /\ st_chunks S3 = st_chunks S1 /\
                from_primary (8 * cap2R cap + cf_head) = true /\
                YG00cf.exh_mem_cf S3 (chunk_class (8 * cap2R cap + cf_head)) = true) /\
             rd32 (aview SEGS (w_H W3) mem3) (as_errno B) 12 /\
             prh_ledger B ly3 S3 Hp3 W3 mem3 ((res, 56 * cap2R cap) :: Lr)
                (if cap =? 0 then Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                    (Z.min SIZE_MAXZ (Ledger.lsum ((res, 56 * cap2R cap) :: Lr) + 8 * cap2R cap))
                 else Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                    (Z.min SIZE_MAXZ (Ledger.lsum ((res, 56 * cap2R cap) :: Lr) - 8 * cap + 8 * cap2R cap)))
                ((cnt + 1 + 1) mod 2 ^ 64) fail (if 8 * cap2R cap <=? most then 1 else ran) most own))).
                (* the text's keys refused arm, the callee's values verbatim *)
         { destruct ARMS2 as [(Hk0 & HAPk) | [(_ & Hcf2 & Hr0 & EHp3 & Eab3 & Hb3 & HL3) |
             [(Hpk0 & Hcf2 & Hr0 & PHp3 & Eab3 & Hb3 & HNP & HER3 & HL3) |
              (_ & _ & Hr16' & _ & l1' & l2' & _ & _ & _ & (b1' & b2' & _ & _ & Hperm3) & _)]]].
           - assert (Hb3 : bytes_at W3 mem3 keys oldy) by (rewrite (Hoy0 Hk0); intros j Hj; cbn [length] in Hj; flia).
             destruct HAPk as [(Hcf2 & Hr0 & EHp3 & Eab3 & HL3) | [(Hcf2 & Hr0 & EHp3 & Eab3 & HNP & HER3 & HL3) |
               (_ & Hr16' & _ & _ & _ & Eab3 & _)]].
             + split; [exact Eab3|]. split; [rewrite EHp3; apply Permutation_refl|]. split; [exact Hb3|].
               left. split; [exact Hcf2|]. rewrite Hcnt2 in HL3. exact HL3.
             + split; [exact Eab3|]. split; [rewrite EHp3; apply Permutation_refl|]. split; [exact Hb3|].
               right. split; [exact Hcf2|]. split; [destruct HNP as (rgc & mc & dc & Wc & cc & HNP);
                 exists S2; exact (grow_null_wf B _ _ _ _ _ _ _ _ _ _ _ HNP)|].
               (* keys = 0 only at cap = 0 (a live keys block is at least 4096 + cf_head), so k = 8 cap = 0 and
                  prh_alloc_post's `lsum + n` is the earlier statement's `lsum - 8 cap + n` *)
               assert (Hc0k : cap = 0).
               { destruct (Z.eq_dec cap 0) as [Hz | Hcn]; [exact Hz | exfalso].
                 assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
                 unfold prh_lin in Hky. pose proof HLED as (_ & _ & HFl & _).
                 pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hb' & _).
                 cbn [fst snd] in Hk, Hb'.
                 destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). flia. }
               split; [exact HER3|]. rewrite (proj2 (Z.eqb_eq cap 0) Hc0k). exact HL3.
             + exfalso. assert (Hin3 : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
                 by (rewrite Eab3; apply in_or_app; right; left; reflexivity).
               destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hbc & _).
               assert (Hrq0 : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
                 by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); flia).
               rewrite unsigned_lit_small in Hres0k by flia. flia.
           - split; [exact Eab3|]. split; [rewrite EHp3; apply Permutation_refl|]. split; [exact Hb3|].
             left. split; [exact Hcf2|]. rewrite Hcnt2 in HL3. exact HL3.
           - split; [exact Eab3|]. split; [exact PHp3|]. split; [exact Hb3|].
             right. split; [exact Hcf2|]. split; [exists S2; exact HNP|].
             assert (Hc0k : cap <> 0) by (intros Hz; exact (Hpk0 (proj2 (Hcap0 Hz) Hty6))).
             split; [exact HER3|]. rewrite (proj2 (Z.eqb_neq cap 0) Hc0k). exact HL3.
           - exfalso. assert (Hin3 : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
               by (apply (Permutation_in _ (Permutation_sym Hperm3)); left; reflexivity).
             destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hbc & _).
             assert (Hrq0 : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
               by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); flia).
             rewrite unsigned_lit_small in Hres0k by flia. flia. }
         destruct HNULL as (Eab3 & PHp3 & Hyb3 & HARMS).
         assert (HAT3 : prhReader_at B ly3 S3 ((res, 56 * cap2R cap) :: Lr) regs e v 56)
           by exact (prhReader_at_eq ly2 S2 _ ly3 S3 regs e v 56 Eab3 Efrs3 Efa3 HAT2).
         paj_run_tok_x_inv (RUNP P PLAW) HS5 HJ3 SHOK5 HPM grow_Bspan.
         { apply (grow_awr_ok_stk _ _ _ 80); [flia | exact FS | exact He0 | grow_wr_stk U2'']. }
         lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W3) mem3) _ |- _ => rename Hf into HFr9 end.
         lazymatch goal with Hg : mem_grows (mrestrict (w_H W3) mem3) _ |- _ => rename Hg into HG9 end.
         destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 Ek3 _ W3 mem3 mem3 md3 _ _
           (spZ regs) v FP ly S Hp W mem md ly3 S3 Hp3
           ltac:(flia) FS KCk (fun _ _ => eq_refl) (fun _ H => H) HAR HARr3 Hceil3 Hslo3 Hshi3 HFr9 HG9
           ltac:(grow_wr_tac U2'' U10'') (same_but_materialized_wvb_any _ mat3)) as (K9 & F9 & G9).
         unfold fpostWmR, fpostWR.
         eapply (grow_ret B ARx SK LAWS PL_grow (@STK_grow prh_img_A) W3 Ek3 _ _ _ e FP regs (grow_extra ty kids keys n cap)
           ly S Hp W mem md (grow_OR v) FP ly3 S3 Hp3 _ _ ltac:(flia) HS5 eq_refl ltac:(vm_compute; reflexivity));
           [ split; [intros nn Hnn; rewrite ?AG3, ?AG2 by flia; subst E; rewrite ?Eimg_low by (unfold A_TEXT; flia);
                     reflexivity
                    | subst Ek3 E2 E; reflexivity]
           | vm_compute; reflexivity
           | reflexivity
           | exact Hra
           | exact HJ3
           | exact K9
           | intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]
           | ].
         intros mat'. unfold fQmn. split; [|exact (PEND _ HPM)]. unfold gr_Q, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7. cbv beta.
         prreg HS5 (10%bv : bv 5) R10f.
         lazymatch type of HS5 with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := ms_mem msF) in * end.
         assert (NW9 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
           mrestrict (w_H W3) mF (Z_to_bv 64 a) = mrestrict (w_H W3) mem3 (Z_to_bv 64 a)).
         { intros a Ha Hnf. subst mF. rewrite (HFr9 (Z_to_bv 64 a)); [reflexivity|].
           rewrite unsigned_lit_small by flia. intros (r & Hin & Hr). vm_compute in Hin.
           repeat (destruct Hin as [Hin | Hin];
                   [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U2'' in Hr; flia |]).
           contradiction. }
         assert (AV9 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 80 <= a < spZ regs) ->
           aview SEGS (w_H W3) mF a = aview SEGS (w_H W3) mem3 a) by (intros a Ha Hnf; apply aview_eq_of; exact (NW9 a Ha Hnf)).
         assert (PR9 : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mF a).
         { intros a Ha. subst mF. eapply apresent_grows; [exact HG9 | exact Ha]. }
         assert (HDRF : pj_hdrR SEGS (mrestrict (w_H W3) mF) v ty num str res keys n cap).
         { apply (pj_hdr_aview (w_H W3) (w_H W3) mem3 mF v ty num str res keys n cap HDR3').
           intros a Ha. split; [apply AV9; flia|]. apply PR9. exact (proj2 (GVK3 a Ha)). }
         assert (HLK9 : forall pk cn fl rn, prh_ledger B ly3 S3 Hp3 W3 mem3 ((res, 56 * cap2R cap) :: Lr) pk cn fl rn most own ->
                          prh_ledger B ly3 S3 Hp3 W3 mF ((res, 56 * cap2R cap) :: Lr) pk cn fl rn most own).
         { intros pk cn fl rn HL3. eapply prh_ledger_keep; [exact HL3|]. intros a Hca.
           destruct (grow_cell_apart B ARx LAWS pst_img 80 ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _ regs e v a
             ltac:(flia) HAR3 HL3 HAT3 Hsp128 Hoff Hca) as (Ha64 & Hnw).
           apply NW9; [flia | unfold grow_wr in Hnw; flia]. }
         assert (HSHK9 : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
                           aview SEGS (w_H W3) mF s = aview SEGS (w_H W3) mem3 s).
         { intros s Hs. apply AV9; unfold SHADOW_OFF in Hs; flia. }
         assert (HKBF : bytes_at W3 mF res kb).
         { apply (bytes_at_aview W3 W3 mem3 mF res kb HB3). intros a Ha. apply AV9; flia. }
         assert (HYBF : bytes_at W3 mF keys yb).
         { destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
           - destruct yb; [intros j Hj; cbn [length] in Hj; flia | cbn [length] in Hyb_len; flia].
           - assert (Eoy : oldy = yb) by (subst oldy; destruct (Z.eqb_spec cap 0); [flia | reflexivity]).
             rewrite Eoy in Hyb3. apply (bytes_at_aview W3 W3 mem3 mF keys yb Hyb3). intros a Ha.
             assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
             unfold prh_lin in Hky. pose proof HLED as (_ & _ & HFl & _).
             pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (_ & Hbk & _). cbn [fst snd] in Hbk.
             destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & _ & Hbc & _).
             assert (Hrqk : 8 * cap + cf_head <= req_size (8 * cap + cf_head))
               by (unfold req_size; destruct (Z.eqb_spec (8 * cap + cf_head) 0); flia).
             apply AV9; flia. }
         assert (HVISF : prhReader_vis W3 mF res (56 * cap2R cap)).
         { assert (HL3any : exists pk cn fl rn, prh_ledger B ly3 S3 Hp3 W3 mem3 ((res, 56 * cap2R cap) :: Lr) pk cn fl rn most own)
             by (destruct HARMS as [(_ & HL3) | (_ & _ & _ & HL3)]; do 4 eexists; exact HL3).
           destruct HL3any as (pk & cn & fl & rn & HL3).
           pose proof HL3 as (_ & _ & HFl3 & _).
           pose proof (proj1 (Forall_forall _ _) HFl3 (res, 56 * cap2R cap) (or_introl eq_refl)) as (_ & Hb3' & Hh3 & _).
           cbn [fst snd] in Hb3', Hh3.
           assert (Hres8 : res mod 8 = 0) by (clear - Hrm; Z.div_mod_to_equations; lia).
           assert (Hn8 : (56 * cap2R cap) mod 8 = 0) by (clear; Z.div_mod_to_equations; lia).
           destruct (hblock_vis ly3 S3 Hp3 W3 mem3 md3 res (56 * cap2R cap) HAR3 Hb3' Hh3 Hres8 Hn8 ltac:(flia))
             as (HRAn & HVn).
           exact (vis_keep _ _ res (56 * cap2R cap) HSHK9 ltac:(flia) ltac:(flia) HRAn HVn). }
         split; [exact HROOM3|].
         split; [rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6); exact (grow_hull_two S S2 S3 cap HHUk1 HHUy1)|].
         split.
         { rewrite Heq, grow_held_eq by flia. rewrite (proj2 (Z.eqb_eq ty 6) Hty6).
           rewrite (blocks_bytes_bsum B ly3 S3), Eab3, <- (blocks_bytes_bsum B ly2 S2). flia. }
         destruct HARMS as [(Hcf2 & HL3) | (Hcf2 & HNP & HER3 & HL3)].
         ++ (* the keys realloc is the chosen failure: arm 5 *)
            right; right; right; right; left.
            split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcf2|].
            split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
            exists res, ((res, 56 * cap2R cap) :: Lr).
            split; [exact Hr16|]. split; [exact Hrm|].
            split.
            { split; [exists blr; split; [exact PAB1 | rewrite Eab3; exact PAB2]|].
              split; [exists hlr; split; [exact PHP | eapply perm_trans; [exact PHp3 | rewrite EHp2; apply Permutation_refl]]|].
              exists Lr. split; [exact PLam | apply Permutation_refl]. }
            split; [exact (HLK9 _ _ _ _ HL3)|].
            split; [exact HKBF|]. split; [exact HVISF|]. split; [exact HYBF|]. split; [exact HDRF|].
            (* outcomes [true; false]: E = the kids realloc's event; the keys realloc's NULL makes none (S3's blocks are S2's) *)
            rewrite Heq, grow_evs_tf. split.
            { rewrite (grow_rs_live_ab B ly3 S3), Eab3, <- (grow_rs_live_ab B ly2 S2). exact HLV2. }
            intros sm x os i H0 hist Hpos Hrun.
            destruct (HPOSK sm x os i H0 hist Hpos Hrun) as (h2 & Hh2).
            destruct (POS0y Hr0y sm x os (i + 1)%nat H0 h2 Hh2 eq_refl) as (h3 & Hh3).
            cbn [length] in Hh3 |- *. rewrite Nat.add_0_r in Hh3. exists h3. exact Hh3.
         ++ (* the keys realloc is refused: arm 6 *)
            right; right; right; right; right; left.
            split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcf2|].
            split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
            exists res, ((res, 56 * cap2R cap) :: Lr).
            split; [exact Hr16|]. split; [exact Hrm|].
            split.
            { split; [exists blr; split; [exact PAB1 | rewrite Eab3; exact PAB2]|].
              split; [exists hlr; split; [exact PHP | eapply perm_trans; [exact PHp3 | rewrite EHp2; apply Permutation_refl]]|].
              exists Lr. split; [exact PLam | apply Permutation_refl]. }
            split; [exact HNP|].
            split.
            { pose proof (pal_env B TL) as ((Her0 & Her1) & _).
              apply (rd32_aview _ _ _ _ HER3). intros x Hx. apply AV9; unfold kLowMemEnd in Her1; flia. }
            (* THE OUTCOME EXCLUSION of the keys refused arm: at a model run whose next events are the all-granted ones
               [kids; keys] with consumer allocations, the kids grant moves the position to S2 (HPOSK) and the keys realloc's
               own outcome clause (cnt + 1 <> fail) says the instance granted, but res2 = 0 *)
            split.
            { intros sm x os i H0 hist Hpos Hrun Hcons.
              rewrite (proj2 (Z.eqb_eq ty 6) Hty6), Heq, grow_evs_all in Hrun, Hcons.
              apply (proj1 (PRH_Base.prh_run_at_app_iff sm x os i [prhPg_ev 56 cap] [prhPg_ev 8 cap])) in Hrun as (Hr1 & Hr2).
              apply (proj1 (PRH_Base.prh_cons_from_app_iff sm x os i 1 1)) in Hcons as (_ & Hc2).
              cbn [length] in Hr2.
              destruct (HPOSK sm x os i H0 hist Hpos Hr1) as (h2 & Hh2).
              revert Hr2. unfold prhPg_ev. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; intros Hr2.
              { destruct (OUTMy (proj2 (Hcap0 Hc0) Hty6) sm x os (i + 1)%nat H0 h2 Hh2 Hr2 Hc2 Hcf2) as (Hrn & _).
                exact (Hrn Hr0y). }
              { assert (Hk0n : keys <> 0).
                { assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
                  unfold prh_lin in Hky. pose proof HLED as (_ & _ & HFl & _).
                  pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
                  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). flia. }
                destruct (OUTRy Hk0n sm x os (i + 1)%nat H0 h2 Hh2 Hr2 Hc2 Hcf2) as (Hrn & _). exact (Hrn Hr0y). } }
            split; [exact (HLK9 _ _ _ _ HL3)|].
            split; [exact HKBF|]. split; [exact HVISF|]. split; [exact HYBF|]. split; [exact HDRF|].
            (* outcomes [true; false]: E = the kids realloc's event; the keys realloc's NULL makes none (S3's blocks are S2's) *)
            rewrite Heq, grow_evs_tf. split.
            { rewrite (grow_rs_live_ab B ly3 S3), Eab3, <- (grow_rs_live_ab B ly2 S2). exact HLV2. }
            intros sm x os i H0 hist Hpos Hrun.
            destruct (HPOSK sm x os i H0 hist Hpos Hrun) as (h2 & Hh2).
            destruct (POS0y Hr0y sm x os (i + 1)%nat H0 h2 Hh2 eq_refl) as (h3 & Hh3).
            cbn [length] in Hh3 |- *. rewrite Nat.add_0_r in Hh3. exists h3. exact Hh3.
      -- (* the keys moved: store them at v + 32, cap' at v + 48, return 0 (grow's arm 7) *)
         lazymatch goal with Hb : branch_taken BC_EQ _ _ = false |- _ => rename Hb into Hres2 end.
         pose proof HK3 as HK3k.
         destruct HK3 as (res2 & H10r2 & HROOM3 & HHU2 & POS0y & POSMy & POSRy & OUTMy & OUTRy & ARMS2).
         assert (HHUy1 : PresetHullBudget.hull_used S2 S3 [prhPg_ev 8 cap])
           by (rewrite <- (grow_hull_ev keys 8 cap HKCy); exact HHU2).
         assert (Hres2ne : res2 <> 0).
         { intros Hz. rewrite branch_eq_U in Hres2. apply Z.eqb_neq in Hres2. apply Hres2.
           rewrite (U_lit Ek3 0) by flia. rewrite U_SOff, E60, H10r2, Hz. unfold w64.
           rewrite unsigned_lit_small by flia. rewrite Z.add_0_r.
           first [reflexivity | (unfold zcanon, M64; reflexivity)]. }
         assert (Hcnt2 : (cnt + 1 + 1) mod 2 ^ 64 = cnt + 2) by (rewrite Z.mod_small; flia).
         assert (HLAM2 : forall a kk, In (a, kk) ((res, 56 * cap2R cap) :: Lr) ->
                           In (a - cf_head, kk + cf_head) (ablocks B ly2 S2)).
         { intros a kk Hin. pose proof HL2 as (_ & _ & HFl & _).
           exact (proj1 (proj2 (proj1 (Forall_forall _ _) HFl (a, kk) Hin))). }
         (* ---- what the keys call left, in one form for its two shapes ---- *)
         assert (COM2 : exists Lr2 blr2 hlr2,
           Permutation ((res, 56 * cap2R cap) :: Lr) (keys_blkR ty keys cap ++ Lr2) /\
           Permutation (ablocks B ly2 S2) (prhReader_ab (keys_blkR ty keys cap) ++ blr2) /\
           Permutation (ablocks B ly3 S3) ((res2 - cf_head, 8 * cap2R cap + cf_head) :: blr2) /\
           Permutation Hp2 (prhReader_hd (keys_blkR ty keys cap) ++ hlr2) /\ Hp3 = (res2 - cf_head) :: hlr2 /\
           prh_ledger B ly3 S3 Hp3 W3 mem3 ((res2, 8 * cap2R cap) :: Lr2)
             (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr))) (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2)))
             (cnt + 2) fail ran most own /\
           prhReader_at B ly3 S3 ((res2, 8 * cap2R cap) :: Lr2) regs e v 56 /\
           (forall x, res2 - cf_head <= x < res2 - cf_head + req_size (8 * cap2R cap + cf_head) -> ~ (v <= x < v + 56)) /\
           bytes_at W3 mem3 res2 yb /\ prhReader_vis W3 mem3 res2 (8 * cap2R cap) /\
           4096 + cf_head <= res2 /\ res2 mod 16 = 0 /\ cnt + 1 <> fail /\
           blocks_bytes S3 <= blocks_bytes S2 + 8 * (cap2R cap - cap) + cf_head).
         { destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0].
           - (* cap = 0: keys is NULL, fuzz_malloc's post *)
             assert (Hk0 : keys = 0) by exact (proj2 (Hcap0 Hc0) Hty6).
             assert (Eky : keys_blkR ty keys cap = []) by (unfold keys_blkR; rewrite (proj2 (Z.eqb_eq cap 0) Hc0); reflexivity).
             destruct ARMS2 as [(_ & HAPk) | [(Hp0 & _) | [(Hp0 & _) | (Hp0 & _)]]];
               [| exfalso; exact (Hp0 Hk0) | exfalso; exact (Hp0 Hk0) | exfalso; exact (Hp0 Hk0)].
             destruct HAPk as [(_ & Hr0 & _) | [(_ & Hr0 & _) |
               (Hcf2 & Hr16' & Hrm' & Hnin' & EHp3 & Eab3 & HRA3 & HVIS3 & (lnew & Hlnew & Hbnew) & HL3)]];
               [exfalso; exact (Hres2ne Hr0) | exfalso; exact (Hres2ne Hr0) |].
             assert (Eyb0 : yb = []) by (destruct yb; [reflexivity | cbn [length] in Hyb_len; flia]).
             assert (Hnn1 : 0 <= 8 * cap2R cap) by flia.
             assert (Hnh1 : 0 <= 8 * cap2R cap + cf_head) by flia.
             pose proof (grow_alloc_fresh ly2 S2 ly3 S3 Hp3 W3 mem3 md3 (res2 - cf_head) (8 * cap2R cap + cf_head) HAR3
               Hnh1 Eab3) as Hfresh1.
             assert (HAT3 : prhReader_at B ly3 S3 ((res2, 8 * cap2R cap) :: (res, 56 * cap2R cap) :: Lr) regs e v 56)
               by exact (grow_at_kept0 B ARx ly2 S2 Hp2 W2 (ms_mem ms3) _ ly3 S3 Hp3 W3 mem3 md3 _ regs e v
                           (8 * cap2R cap) res2 HARc2 HAR3 HAT2 Eab3 Efrs3 Efa3 Hfresh1).
             assert (HAPn2 : forall x, res2 - cf_head <= x < res2 - cf_head + req_size (8 * cap2R cap + cf_head) ->
                               ~ (v <= x < v + 56))
               by exact (grow_new_apart0 ly2 S2 Hp2 W2 (ms_mem ms3) _ ly3 S3 Hp3 W3 mem3 md3 _ regs e v
                           (8 * cap2R cap) res2 HARc2 HAR3 HLAM2 HAT2 Eab3 Efrs3 Efa3 Hsp0 Hnn1).
             exists ((res, 56 * cap2R cap) :: Lr), (ablocks B ly2 S2), Hp2.
             rewrite Eky. unfold prhReader_ab, prhReader_hd. cbn [map app].
             split; [apply Permutation_refl|]. split; [apply Permutation_refl|].
             split; [rewrite Eab3; apply Permutation_sym, Permutation_cons_append|].
             split; [apply Permutation_refl|]. split; [exact EHp3|].
             split.
             { replace (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                         (Ledger.lsum ((res2, 8 * cap2R cap) :: (res, 56 * cap2R cap) :: Lr)))
                 with (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                         (Ledger.lsum ((res, 56 * cap2R cap) :: Lr) + 8 * cap2R cap)) by (cbn [Ledger.lsum]; flia).
               rewrite <- Hcnt2. exact HL3. }
             split; [exact HAT3|]. split; [exact HAPn2|].
             split; [rewrite Eyb0; intros j Hj; cbn [length] in Hj; flia|].
             split; [split; [exact HRA3 | exact HVIS3]|].
             split; [exact Hr16'|]. split; [exact Hrm'|]. split; [exact Hcf2|].
             rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly2 S2), Eab3, bsum_app. cbn [bsum fold_right snd].
             rewrite Hc0. unfold cap2R. cbn [Z.eqb]. flia.
           - (* cap <> 0: fuzz_realloc's SUCCESS arm on the keys block *)
             assert (Hcp : 0 < cap) by flia.
             destruct (Hcapp Hcp) as (Hink & Hky). specialize (Hky Hty6). unfold prh_lin in Hink, Hky.
             assert (Hky2 : In (keys, 8 * cap) Lr).
             { apply (Permutation_in _ PLam) in Hky. unfold kids_blkR in Hky. rewrite (proj2 (Z.eqb_neq cap 0) Hc0) in Hky.
               destruct Hky as [Hq | Hky]; [injection Hq as Ek Ekk; flia | exact Hky]. }
             pose proof HL2 as (_ & _ & HFl2 & _).
             pose proof (proj1 (Forall_forall _ _) HFl2 (keys, 8 * cap) (or_intror Hky2)) as (_ & Hbk2 & Hhk2 & _).
             cbn [fst snd] in Hbk2, Hhk2.
             destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR2 Hbk2) as (_ & Hbk4096 & _).
             assert (Hkeys0 : keys <> 0) by flia.
             assert (Eoy : oldy = yb) by (subst oldy; destruct (Z.eqb_spec cap 0); [flia | reflexivity]).
             assert (Eky : keys_blkR ty keys cap = [(keys, 8 * cap)]).
             { unfold keys_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), (proj2 (Z.eqb_eq ty 6) Hty6). reflexivity. }
             destruct ARMS2 as [(Hp0 & _) | [(_ & _ & Hr0 & _) | [(_ & _ & Hr0 & _) |
               (_ & Hcf2 & Hr16' & Hrm' & l1' & l2' & ELam2 & Hnin' & EHp3 & (b1' & b2' & Eab2' & Hfresh3 & Hperm3)
                & (rest' & Hlr' & Hbr') & HRA3 & HVIS3 & HL3)]]];
               [exfalso; exact (Hkeys0 Hp0) | exfalso; exact (Hres2ne Hr0) | exfalso; exact (Hres2ne Hr0) |].
             assert (Hinky2 : In (keys, 8 * cap) ((res, 56 * cap2R cap) :: Lr))
               by (rewrite ELam2; apply in_or_app; right; left; reflexivity).
             assert (HAPky : forall x, pj_holdsR (keys, 8 * cap) x -> ~ (v <= x < v + 56)).
             { intros x Hx. apply (HAP (keys, 8 * cap) x); [|exact Hx].
               unfold kids_blkR. rewrite (proj2 (Z.eqb_neq cap 0) Hc0), Eky. right; left; reflexivity. }
             assert (HAT3 : prhReader_at B ly3 S3 ((res2, 8 * cap2R cap) :: l1' ++ l2') regs e v 56)
               by exact (grow_at_kept B ARx ly2 S2 Hp2 W2 (ms_mem ms3) _ ly3 S3 Hp3 W3 mem3 md3 _ l1' l2' regs e v
                           keys (8 * cap) (8 * cap2R cap) res2 b1' b2' HARc2 HAR3 HLAM2 HAT2 HAPky ELam2 Eab2' Hperm3
                           Efrs3 Efa3 Hfresh3).
             assert (HAPn2 : forall x, res2 - cf_head <= x < res2 - cf_head + req_size (8 * cap2R cap + cf_head) ->
                               ~ (v <= x < v + 56))
               by exact (grow_new_apart ly2 S2 Hp2 W2 (ms_mem ms3) _ ly3 S3 Hp3 W3 mem3 md3 _ regs e v keys (8 * cap)
                           (8 * cap2R cap) res2 b1' b2' HARc2 HAR3 HLAM2 HAT2 HAPky Hinky2 Eab2' Hperm3 Efrs3 Efa3
                           Hfresh3 Hsp0).
             assert (Hc2c : cap2R cap = 2 * cap) by (unfold cap2R; rewrite (proj2 (Z.eqb_neq cap 0) Hc0); reflexivity).
             assert (HB3y : bytes_at W3 mem3 res2 yb).
             { rewrite Eoy, Z.min_l, firstn_all2 in Hbr' by flia. exact (bytes_at_prefix W3 mem3 res2 yb rest' Hbr'). }
             exists (l1' ++ l2'), (b1' ++ b2'), (remove Z.eq_dec (keys - cf_head) Hp2).
             rewrite Eky. unfold prhReader_ab, prhReader_hd. cbn [map app fst snd].
             split; [rewrite ELam2; apply Permutation_sym, Permutation_middle|].
             split; [rewrite Eab2'; apply Permutation_sym, Permutation_middle|].
             split; [exact Hperm3|].
             split; [exact (perm_remove_nodup Hp2 _ (ledger_hp_nodup B _ _ _ _ _ _ _ _ _ _ _ _ HL2) Hhk2)|].
             split; [exact EHp3|].
             split.
             { replace (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                         (Ledger.lsum ((res2, 8 * cap2R cap) :: l1' ++ l2')))
                 with (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                         (Ledger.lsum (l1' ++ l2') + 8 * cap2R cap)) by (cbn [Ledger.lsum]; flia).
               rewrite <- Hcnt2. exact HL3. }
             split; [exact HAT3|]. split; [exact HAPn2|]. split; [exact HB3y|].
             split; [split; [exact HRA3 | exact HVIS3]|].
             split; [exact Hr16'|]. split; [exact Hrm'|]. split; [exact Hcf2|].
             rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hperm3), Eab2', !bsum_app,
               !bsum_cons, !bsum_app. cbn [snd]. flia. }
         destruct COM2 as (Lr2 & blr2 & hlr2 & PLam2 & PAB3 & PAB4 & PHP2 & EHp3 & HL3 & HAT3 & HAPn2 & HB3y & HVIS3y
           & Hr16' & Hrm' & Hcf2 & HBB3).
         (* ---- the node's shadow and place after the keys call ---- *)
         assert (HRAk3 : range_addressable (aview SEGS (w_H W2) (ms_mem ms3)) SHADOW_OFF v 56).
         { pose proof SHOK4 as SH0. unfold sh_ok, grow_SH in SH0. apply Forall_inv in SH0. destruct SH0 as (HR & _).
           unfold grow_Bx in HR. cbn [she_m she_lo she_hi] in HR.
           rewrite !U_SOff, U32', U10', !Z.add_0_r, !zcanon_id in HR by (unfold M64, SHADOW_OFF; flia).
           exact HR. }
         assert (HFPappk : forall a, inFP FP1k a -> app_addr a).
         { intros a (r & Hr & Hra'). subst FP1k. destruct (Z.eqb_spec keys 0) as [Hk0 | Hk0]; [destruct Hr|].
           unfold ablocks_fp in Hr. cbn [map fst snd In] in Hr. destruct Hr as [<- | []].
           cbn [fst snd] in Hra'.
           assert (Hck : cap <> 0) by (intros Hz; apply Hk0; exact (proj2 (Hcap0 Hz) Hty6)).
           assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6). unfold prh_lin in Hky.
           pose proof HLED as (_ & _ & HFl & _).
           pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (_ & Hbk & _). cbn [fst snd] in Hbk.
           destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hbk) as (_ & _ & _ & Hiapp & _).
           exact (in_app_addr _ _ a Hiapp ltac:(flia)). }
         assert (Hlo3 : ly_stk_lo ly3 <= spZ regs) by flia.
         assert (Hhi3 : spZ regs + e <= ly_stk_hi ly3) by (rewrite Ehi3; flia).
         assert (HRA3v : range_addressable (aview SEGS (w_H W3) mem3) SHADOW_OFF v 56)
           by exact (grow_v_shadow2 B ARx SK LAWS ly2 S2 Hp2 W2 (ms_mem ms3) _ ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _ regs e v
                       _ _ FP1k k3 HARc2 HAR3 HL3 HAT3 Hlo3 Hhi3 HRAk3 HJ1k HFPappk).
         assert (Hvloc3 : grow_vloc B ly3 S3 regs e v)
           by exact (grow_vloc2_nf ly2 S2 Hp2 W2 (ms_mem ms3) _ _ _ _ _ _ _ _ regs e v _ _ FP1k ly3 S3 Hp3 W3 mem3 md3 k3
                       HARc2 HL2c HAT2 HJ1k HnFk).
         assert (HvlocJ3 : (exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= v /\ v + 56 <= b + req_size m) \/
           (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly3 cid pos <= v /\
              v + 56 <= frame_addr ly3 cid pos + fs_frame_bytes cid) \/ (spZ regs <= v /\ v + 56 <= spZ regs + e)).
         { destruct Hvloc3 as [Hb | [(cid & pos & Hf & H1 & H2) | Hx]];
             [left; exact Hb | right; left; exists cid, pos; rewrite <- Efrs, <- Efrs3; exact (conj Hf (conj H1 H2))
             | right; right; exact Hx]. }
         (* ---- the re-seat: the node's two regions (the kids field now holds res), the shadow entry ---- *)
         pose proof HDR3' as ((_ & HRW3) & (_ & Vty3) & _ & _ & (_ & Vk3) & (_ & Vy3') & (_ & Vn3) & (_ & Vc3')).
         assert (DV3 : forall k w, (k < 40)%nat -> ew E k = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 ->
           sv_denot Ek3 (SOff k 0) = Z_to_bv 64 w).
         { intros k w Hk Hkw Hw. cbn [sv_denot]. rewrite AG3 by flia. rewrite AG2 by exact Hk.
           rewrite Hkw, unsigned_lit_small by exact Hw. rewrite Z.add_0_r. reflexivity. }
         assert (D44' : sv_denot Ek3 (SOff 44 0) = Z_to_bv 64 res).
         { cbn [sv_denot]. rewrite AG3 by flia. rewrite E44, H10r. unfold w64. rewrite unsigned_lit_small by flia.
           rewrite Z.add_0_r. reflexivity. }
         assert (U241'' : bv_unsigned (ew Ek3 241) = VAL (A_OBJ 0))
           by (subst Ek3; rewrite ew_havoc_hi by (rewrite length_map; cbn; flia); exact U241').
         assert (U253'' : bv_unsigned (ew Ek3 253) = VAL (A_OBJ 12))
           by (subst Ek3; rewrite ew_havoc_hi by (rewrite length_map; cbn; flia); exact U253').
         assert (U32'' : bv_unsigned (ew Ek3 32) = SHADOW_OFF) by (rewrite AG3 by flia; exact U32').
         set (grow_vA3 := YP09.mkRegion (Some 10%nat) 0 40 24 40
           [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 44 0));
            YP09.mkChunk 32 (CVal 8 (SOff 35 0))]).
         assert (RB3 : region_ok SEGS Ek3 (mrestrict (w_H W3) mem3) grow_vB).
         { unfold grow_vB, region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10''.
           split; [flia|]. split; [flia|]. split; [intros o Ho; apply HRW3; flia|].
           repeat apply Forall_cons; try apply Forall_nil.
           - apply (chunk_ok_val SEGS Ek3 _ v 40 8 (SOff 36 0) n); [apply DV3; [flia | exact E36 | flia] | exact Hn | flia
               | exact Vn3].
           - apply (chunk_ok_val SEGS Ek3 _ v 48 8 (SOff 37 0) cap); [apply DV3; [flia | exact E37 | flia] | exact Hcap | flia
               | exact Vc3']. }
         assert (RA3 : region_ok SEGS Ek3 (mrestrict (w_H W3) mem3) grow_vA3).
         { subst grow_vA3. unfold region_ok.
           cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U10''.
           split; [flia|]. split; [flia|]. split; [intros o Ho; apply HRW3; flia|].
           repeat apply Forall_cons; try apply Forall_nil.
           - apply (chunk_ok_val SEGS Ek3 _ v 0 4 (SOff 33 0) ty); [apply DV3; [flia | exact E33 | flia] | exact Hty | flia |].
             rewrite Z.add_0_r. exact Vty3.
           - apply (chunk_ok_val SEGS Ek3 _ v 24 8 (SOff 44 0) res); [exact D44' | exact Hres64 | flia | exact Vk3].
           - apply (chunk_ok_val SEGS Ek3 _ v 32 8 (SOff 35 0) keys); [apply DV3; [flia | exact E35 | flia] | exact Hkeys | flia
               | exact Vy3']. }
         norm_ss HS5.
         pose proof (st_ok_pi_add_region Ek3 _ _ grow_vB HS5 ltac:(vm_compute; reflexivity) RB3) as HS6.
         match type of HS6 with ?P -> _ => assert (HD : P); [|specialize (HS6 HD); clear HD] end.
         { apply all_disjoint_of_extents.
           lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
           unfold grow_vB. cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
           cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U2'', ?U10'', ?U241'', ?U253''. repeat split; flia. }
         norm_ss HS6. clear HS5.
         pose proof (st_ok_pi_add_region Ek3 _ _ grow_vA3 HS6 ltac:(vm_compute; reflexivity) RA3) as HS7.
         match type of HS7 with ?P -> _ => assert (HD : P); [|specialize (HS7 HD); clear HD] end.
         { apply all_disjoint_of_extents.
           lazymatch goal with |- zall_disjoint _ (map _ ?rs) => let rs' := eval vm_compute in rs in change rs with rs' end.
           subst grow_vA3. cbn [map zall_disjoint]. unfold extent_of_region, zdisj.
           cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U2'', ?U10'', ?U241'', ?U253''. repeat split; flia. }
         subst grow_vA3. norm_ss HS7. clear HS6.
         assert (SHOK7 : sh_ok SEGS grow_Bx grow_SH Ek3 (mrestrict (w_H W3) mem3)).
         { unfold sh_ok, grow_SH. apply Forall_cons; [|apply Forall_nil]. split.
           + unfold grow_Bx. cbn [she_m she_lo she_hi].
             rewrite !U_SOff, U32'', U10'', !Z.add_0_r, !zcanon_id by (unfold M64, SHADOW_OFF; flia).
             change (rd_of SEGS (mrestrict (w_H W3) mem3)) with (aview SEGS (w_H W3) mem3). exact HRA3v.
           + unfold app_apart, grow_Bx. cbn [she_m she_lo she_hi]. intros a Ha.
             rewrite !U_SOff, U32'', U10'', !Z.add_0_r, !zcanon_id in * by (unfold M64, SHADOW_OFF; flia).
             apply Happ. flia. }
         clear SHOK5.
         (* ---- the run: `sd a0, 0(s1)` (the keys store), `sd s6, 0(s0)` (cap'), ret ---- *)
         paj_run_tok_x_inv (RUNP P PLAW) HS7 HJ3 SHOK7 HPM grow_Bspan.
         { apply grow_awr_ok_fr with (v := v) (FR := 80);
             [flia | exact FS | exact He0 | grow_wr U2'' U10'' | apply grow_FP_v | exact HvlocJ3]. }
         lazymatch goal with Hf : frame_of _ _ (mrestrict (w_H W3) mem3) _ |- _ => rename Hf into HFr9 end.
         lazymatch goal with Hg : mem_grows (mrestrict (w_H W3) mem3) _ |- _ => rename Hg into HG9 end.
         destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 Ek3 _ W3 mem3 mem3 md3 _ _
           (spZ regs) v FP ly S Hp W mem md ly3 S3 Hp3
           ltac:(flia) FS KCk (fun _ _ => eq_refl) (fun _ H => H) HAR HARr3 Hceil3 Hslo3 Hshi3 HFr9 HG9
           ltac:(grow_wr_tac U2'' U10'') (same_but_materialized_wvb_any _ mat3)) as (K9 & F9 & G9).
         unfold fpostWmR, fpostWR.
         eapply (grow_ret B ARx SK LAWS PL_grow (@STK_grow prh_img_A) W3 Ek3 _ _ _ e FP regs (grow_extra ty kids keys n cap)
           ly S Hp W mem md (grow_OR v) FP ly3 S3 Hp3 _ _ ltac:(flia) HS7 eq_refl ltac:(vm_compute; reflexivity));
           [ split; [intros nn Hnn; rewrite ?AG3, ?AG2 by flia; subst E; rewrite ?Eimg_low by (unfold A_TEXT; flia);
                     reflexivity
                    | subst Ek3 E2 E; reflexivity]
           | vm_compute; reflexivity
           | reflexivity
           | exact Hra
           | exact HJ3
           | exact K9
           | intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]
           | ].
         intros mat'. unfold fQmn. split; [|exact (PEND _ HPM)]. unfold gr_Q, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7. cbv beta.
         prreg HS7 (10%bv : bv 5) R10f.
         lazymatch type of HS7 with st_ok_pi _ _ _ _ (restrict _ ?msF) => set (mF := ms_mem msF) in * end.
         pose proof (st_ok_region_nth SEGS Ek3 _ _ 0 _ HS7 ltac:(vm_compute; reflexivity)) as RAF.
         pose proof (st_ok_region_nth SEGS Ek3 _ _ 1 _ HS7 ltac:(vm_compute; reflexivity)) as RBF.
         cbn [ms_mem restrict] in RAF, RBF.
         assert (Hres264 : 0 <= res2 < 2 ^ 64).
         { assert (Hin3 : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
             by (apply (Permutation_in _ (Permutation_sym PAB4)); left; reflexivity).
           destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hbc & _).
           assert (Hrq0 : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
             by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); flia). flia. }
         assert (D60 : sv_denot Ek3 (SOff 60 0) = Z_to_bv 64 res2).
         { cbn [sv_denot]. rewrite E60, H10r2. unfold w64. rewrite unsigned_lit_small by flia. rewrite Z.add_0_r. reflexivity. }
         assert (RkF : rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 24) res).
         { split; [exact Hres64|].
           exact (field_of_region SEGS Ek3 _ 10 v _ _ _ _ _ 24 8%N (SOff 44 0) res RAF U10'' ltac:(cbn; tauto) D44'
                    Hres64 ltac:(cbn; flia)). }
         assert (RyF : rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 32) res2).
         { split; [exact Hres264|].
           exact (field_of_region SEGS Ek3 _ 10 v _ _ _ _ _ 32 8%N (SOff 60 0) res2 RAF U10'' ltac:(cbn; tauto) D60
                    Hres264 ltac:(cbn; flia)). }
         assert (Hc64 : 0 <= cap2R cap < 2 ^ 64) by flia.
         assert (RcF : rd_u64 SEGS (mrestrict (w_H W3) mF) (v + 48) (cap2R cap)).
         { split; [exact Hc64|].
           exact (field_of_region SEGS Ek3 _ 10 v _ _ _ _ _ 48 8%N (SOff 38 0) (cap2R cap) RBF U10'' ltac:(cbn; tauto)
                    (DV3 38%nat (cap2R cap) ltac:(flia) E38 Hc64) Hc64 ltac:(cbn; flia)). }
         assert (HSHK9 : forall s, SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 ->
                           aview SEGS (w_H W3) mF s = aview SEGS (w_H W3) mem3 s).
         { intros s Hs. apply aview_eq_of. apply F9. rewrite unsigned_lit_small by (unfold SHADOW_OFF in Hs; flia).
           unfold grow_wr. intros [Hw | [Hw | Hw]]; [unfold SHADOW_OFF in Hs; flia | |];
             exact (Happ s ltac:(flia) Hs). }
         (* the new keys block: below alloc_ceiling and apart from the node *)
         assert (Hnew3y : In (res2 - cf_head, 8 * cap2R cap + cf_head) (ablocks B ly3 S3))
           by (apply (Permutation_in _ (Permutation_sym PAB4)); left; reflexivity).
         destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR3 Hnew3y) as (_ & _ & Hncy & _).
         assert (Hrqy : 8 * cap2R cap + cf_head <= req_size (8 * cap2R cap + cf_head))
           by (unfold req_size; destruct (Z.eqb_spec (8 * cap2R cap + cf_head) 0); flia).
         (* the harness list's sums and the kids entry in it *)
         assert (Hlsum2 : 56 * cap2R cap + Ledger.lsum Lr = 8 * cap + Ledger.lsum Lr2).
         { pose proof (grow_lsum_perm _ _ PLam2) as Hq. rewrite grow_lsum_app, (grow_lsum_keys ty keys cap) in Hq by flia.
           cbn [Ledger.lsum] in Hq. flia. }
         assert (Hink3 : In (res, 56 * cap2R cap) ((res2, 8 * cap2R cap) :: Lr2)).
         { right. pose proof (Permutation_in _ PLam2
             (or_introl eq_refl : In (res, 56 * cap2R cap) ((res, 56 * cap2R cap) :: Lr))) as Hq.
           apply in_app_or in Hq as [Hq | Hq]; [|exact Hq].
           exfalso. revert Hq. unfold keys_blkR. destruct ((cap =? 0) || negb (ty =? 6)); [intros []|].
           intros [Hq | []]. injection Hq as _ Hq. flia. }
         assert (HVISk : prhReader_vis W3 mF res (56 * cap2R cap)).
         { pose proof HL3 as (_ & _ & HFl3 & _).
           pose proof (proj1 (Forall_forall _ _) HFl3 _ Hink3) as (_ & Hb3' & Hh3 & _).
           cbn [fst snd] in Hb3', Hh3.
           assert (Hres8 : res mod 8 = 0) by (clear - Hrm; Z.div_mod_to_equations; lia).
           assert (Hn8 : (56 * cap2R cap) mod 8 = 0) by (clear; Z.div_mod_to_equations; lia).
           destruct (hblock_vis ly3 S3 Hp3 W3 mem3 md3 res (56 * cap2R cap) HAR3 Hb3' Hh3 Hres8 Hn8 ltac:(flia))
             as (HRAn & HVn).
           exact (vis_keep _ _ res (56 * cap2R cap) HSHK9 ltac:(flia) ltac:(flia) HRAn HVn). }
         split; [exact HROOM3|].
         split; [rewrite Heq, (proj2 (Z.eqb_eq ty 6) Hty6); exact (grow_hull_two S S2 S3 cap HHUk1 HHUy1)|].
         split.
         { rewrite Heq, grow_held_eq by flia. rewrite (proj2 (Z.eqb_eq ty 6) Hty6). flia. }
         right; right; right; right; right; right.
         split; [exact Heq|]. split; [exact Hcf|]. split; [exact Hty6|]. split; [exact Hcf2|].
         split; [rewrite R10f; apply bv_eq; vm_compute; reflexivity|].
         exists res, res2, ((res2, 8 * cap2R cap) :: Lr2).
         split; [exact Hr16|]. split; [exact Hrm|]. split; [exact Hr16'|]. split; [exact Hrm'|].
         lazymatch goal with |- prhReader_swap ?B' ?a ?b ?c ?d ?e ?f ?g ?h ?D1 ?D2 /\ _ =>
           assert (HSW7 : prhReader_swap B' a b c d e f g h D1 D2) end.
         { (* the two swaps composed *)
           split.
           - assert (Hnk1 : ~ In (res - cf_head, 56 * cap2R cap + cf_head) (prhReader_ab (keys_blkR ty keys cap))).
             { unfold keys_blkR, prhReader_ab. destruct ((cap =? 0) || negb (ty =? 6)); cbn [map In fst snd];
                 [tauto | intros [Hq | []]; injection Hq as _ Hq; flia]. }
             destruct (perm_swap2 (ablocks B ly S) blr blr2 (prhReader_ab (kids_blkR kids cap))
               (prhReader_ab (keys_blkR ty keys cap)) (res - cf_head, 56 * cap2R cap + cf_head) PAB1
               (perm_trans (Permutation_sym PAB2) PAB3) Hnk1) as (Z0 & PZ1 & PZ2).
             exists Z0. unfold prhReader_ab in PZ1 |- *. rewrite map_app. split; [exact PZ1|].
             eapply perm_trans; [exact PAB4|]. cbn [map app fst snd]. apply perm_skip. exact PZ2.
           - split.
             + assert (Hnk2 : ~ In (res - cf_head) (prhReader_hd (keys_blkR ty keys cap))).
               { unfold keys_blkR, prhReader_hd. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [cbn; tauto|].
                 rewrite (proj2 (Z.eqb_eq ty 6) Hty6). cbn [orb negb map In fst]. intros [Hq | []].
                 assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
                 unfold prh_lin in Hky.
                 assert (Hky2 : In (keys, 8 * cap) Lr).
                 { apply (Permutation_in _ PLam) in Hky. unfold kids_blkR in Hky.
                   rewrite (proj2 (Z.eqb_neq cap 0) Hc0) in Hky.
                   destruct Hky as [Hq' | Hky]; [injection Hq' as Ek Ekk; flia | exact Hky]. }
                 pose proof HL2 as (_ & HND2 & _). apply NoDup_ListNoDup in HND2. cbn [map fst] in HND2.
                 apply NoDup_cons_iff in HND2 as (Hnr & _). apply Hnr. replace res with keys by flia.
                 apply in_map_iff. exists (keys, 8 * cap). split; [reflexivity | exact Hky2]. }
               assert (PHP2' : Permutation ((res - cf_head) :: hlr) (prhReader_hd (keys_blkR ty keys cap) ++ hlr2))
                 by (rewrite <- EHp2; exact PHP2).
               destruct (perm_swap2 Hp hlr hlr2 (prhReader_hd (kids_blkR kids cap))
                 (prhReader_hd (keys_blkR ty keys cap)) (res - cf_head) PHP PHP2' Hnk2) as (Z0 & PZ1 & PZ2).
               exists Z0. unfold prhReader_hd in PZ1 |- *. rewrite map_app. split; [exact PZ1|].
               rewrite EHp3. cbn [map app fst snd]. apply perm_skip. exact PZ2.
             + assert (Hnk3 : ~ In (res, 56 * cap2R cap) (keys_blkR ty keys cap)).
               { unfold keys_blkR. destruct ((cap =? 0) || negb (ty =? 6)); cbn [In];
                   [tauto | intros [Hq | []]; injection Hq as _ Hq; flia]. }
               destruct (perm_swap2 Lam Lr Lr2 (kids_blkR kids cap) (keys_blkR ty keys cap) (res, 56 * cap2R cap)
                 PLam PLam2 Hnk3) as (Z0 & PZ1 & PZ2).
               exists Z0. split; [exact PZ1|]. cbn [app]. apply perm_skip. exact PZ2. }
         split; [exact HSW7|].
         split.
         { replace (Z.max peak (Z.max (Ledger.lsum Lam + 56 * (cap2R cap - cap))
                     (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2))))
             with (Z.max (Z.max peak (Ledger.lsum ((res, 56 * cap2R cap) :: Lr)))
                     (Ledger.lsum ((res2, 8 * cap2R cap) :: Lr2))) by (cbn [Ledger.lsum]; flia).
           eapply prh_ledger_keep; [exact HL3|]. intros a Hca.
           destruct (grow_cell_apart B ARx LAWS pst_img 80 ly3 S3 Hp3 W3 mem3 md3 _ _ _ _ _ _ _ regs e v a
             ltac:(flia) HAR3 HL3 HAT3 Hsp128 Hoff Hca) as (Ha64 & Hnw).
           apply F9. rewrite unsigned_lit_small by flia. exact Hnw. }
         split.
         { rewrite Heq, grow_held_only by flia. rewrite (proj2 (Z.eqb_eq ty 6) Hty6). cbn [Ledger.lsum]. flia. }
         split.
         { apply (grow_bytes_keep W3 mem3 mF (spZ regs) v res kb HB3 F9); [flia | flia |].
           intros a Ha. exact (proj2 (HNEWW a ltac:(flia))). }
         split; [exact HVISk|].
         split.
         { apply (grow_bytes_keep W3 mem3 mF (spZ regs) v res2 yb HB3y F9); [flia | flia |].
           intros a Ha. unfold grow_wr. intros Hw.
           assert (Hnv : ~ (v <= a < v + 56)) by (apply HAPn2; flia).
           destruct Hw as [Hw | [Hw | Hw]]; flia. }
         split.
         { destruct HVIS3y as (HRAn & HVn).
           exact (vis_keep _ _ res2 (8 * cap2R cap) HSHK9 ltac:(flia) ltac:(flia) HRAn HVn). }
         split.
         { exact (grow_hdr_keep 80 (w_H W3) mem3 mF (spZ regs) v ty num str res keys n cap res res2 (cap2R cap)
                    HDR3' F9 G9 Hvstk Hv0' Hv64 RkF RyF RcF). }
         split.
         { unfold pj_slots_atR, prh_lin.
           split; [exact Hty56|]. split; [flia|]. split; [intros Hz; flia|].
           intros _. split; [exact Hink3 | intros _; left; reflexivity]. }
         (* outcomes [true; true]: E = both reallocs' events; the live requests move by the two swaps (HSW7,
            PwGrowLive.grow_live_swap2), and the position by the kids leaf's implication, then the keys leaf's *)
         rewrite (proj2 (Z.eqb_eq ty 6) Hty6), Heq, grow_evs_tt. split.
         { rewrite Hty6 in HSW7. exact (grow_live_swap2 B _ _ _ _ _ _ _ _ _ _ _ _ _ HSW7 ltac:(flia)). }
         intros sm x os i H0 hist Hpos Hrun.
         change [prhPg_ev 56 cap; prhPg_ev 8 cap] with ([prhPg_ev 56 cap] ++ [prhPg_ev 8 cap]) in Hrun.
         apply PRH_Base.prh_run_at_app_iff in Hrun as (Hr1 & Hr2). cbn [length] in Hr2.
         destruct (HPOSK sm x os i H0 hist Hpos Hr1) as (h2 & Hh2).
         assert (Hkeys0 : cap <> 0 -> keys <> 0).
         { intros Hc0. assert (Hcp : 0 < cap) by flia. destruct (Hcapp Hcp) as (_ & Hky). specialize (Hky Hty6).
           unfold prh_lin in Hky. pose proof HLED as (_ & _ & HFl & _).
           pose proof (proj1 (Forall_forall _ _) HFl (keys, 8 * cap) Hky) as (Hk & Hb' & _). cbn [fst snd] in Hk, Hb'.
           destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hb') as (_ & Hb4096 & _). flia. }
         revert Hr2. unfold prhPg_ev. destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; intros Hr2.
         { destruct (POSMy Hres2ne (proj2 (Hcap0 Hc0) Hty6) sm x os (i + 1)%nat H0 h2 Hh2 Hr2) as (h3 & Hh3).
           exists h3. cbn [length] in Hh3 |- *. replace (i + 2)%nat with (i + 1 + 1)%nat by lia. exact Hh3. }
         { destruct (POSRy Hres2ne (Hkeys0 Hc0) sm x os (i + 1)%nat H0 h2 Hh2 Hr2) as (h3 & Hh3).
           exists h3. cbn [length] in Hh3 |- *. replace (i + 2)%nat with (i + 1 + 1)%nat by lia. exact Hh3. }
Qed.


(* grow's walk against the kit's tgrow_specX (PRH_FnReader.v f1ae32e3b2cd), AT ONE RECORD: the text's premises at D (gr_pre,
   which tgrow_specX_records below ties to the kit's term) give the text's conclusion at D. No per-call premise:
   against the post-implication leaf (tfuzz_realloc_specX, PRH_FnAlloc 4d8aeba047e5) the keys call needs no position at
   the kids call's post state, so AGREE-PREFIX is NOT used; the inner calls' live counts come from the text's pkR
   premises (PwGrowG.grow_cnt_at) and their live bytes from its live room at each event. The name is kept from the
   entry-keyed form (the lead's rule: keep lemma names). *)
Theorem grow_K0_of_args : forall CTX0 (D : gr_in),
  gr_pre CTX0 D ->
  SRr' SEGS RZ_cf (gi_W D) (cfg_at SEGS (@pa_sigma _ A_prog_listing PI_prog_A AS_grow) (gi_regs D) (gi_mem D) (gi_md D))
    (gr_post D).
Proof.
intros CTX0 D0 HPD.
destruct D0 as [ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own].
pose (D := mkGrIn ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own).
pose proof HPD as HPD'. unfold gr_pre in HPD'. cbn [gi_ly gi_S gi_Hp gi_W gi_regs gi_mem gi_md gi_ch gi_e gi_v gi_ty gi_num gi_str gi_kids gi_keys gi_n gi_cap
  gi_kb gi_yb gi_Lam gi_peak gi_cnt gi_fail gi_ran gi_most gi_own] in HPD'.
destruct HPD' as (HPRE & HCLOS & HCH & HROOM & HPKS & HPK24 & HHULL & H10 & Hv0 & Hv8 & HH & HSLOT & HAP & HWIN & HAT & HRA
  & HOLD & HLED & HCNT & HLIVE).
unfold gr_post, gr_Q, tgrP_Q, tgrP_A1, tgrP_A2, tgrP_A3, tgrP_A4, tgrP_A5, tgrP_A6, tgrP_A7, gr_FP. cbn [gi_ly gi_S gi_Hp gi_W gi_regs gi_mem gi_md gi_ch gi_e gi_v gi_ty gi_num gi_str gi_kids gi_keys gi_n gi_cap
  gi_kb gi_yb gi_Lam gi_peak gi_cnt gi_fail gi_ran gi_most gi_own].
pose proof HPRE as (HPREX & HROD).
pose proof HPREX as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (He0 & He16 & Hetop & Hepres).
assert (FS : 80 <= @STK_grow prh_img_A) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hvloc : grow_vloc B ly S regs e v)
  by exact (grow_vloc_of_at B ly S Hp W mem Lam peak cnt fail ran most own regs e v HLED HAT).
destruct (grow_vbounds B ARx LAWS ly S Hp W mem md (@STK_grow prh_img_A) 80 regs e v
  HAR Hstk ltac:(lia) FS He0 Hetop Hvloc) as (Hv4096 & Hvhi & Hvstk & Hoff & Happ).
assert (Hd0 : v + 56 <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= v)
  by exact (range_apart_img _ _ (cell_img (VAL (A_OBJ 0)) (or_introl eq_refl)) Hoff).
assert (Hd12 : v + 56 <= VAL (A_OBJ 12) \/ VAL (A_OBJ 12) + 8 <= v)
  by exact (range_apart_img _ _ (cell_img (VAL (A_OBJ 12)) (or_intror eq_refl)) Hoff).
destruct (grow_entry ly S Hp W regs mem md ch v ty num str kids keys n cap
  HPREX H10 Hv8 Hv4096 Hvhi Hvstk Hd0 Hd12 Happ HH HRA) as [HS SHOK].
(* the widened journal of the caller-window form, at the entry state *)
set (FP := [(v + 24, v + 40); (v + 48, v + 56)] ++
           ablocks_fp (prhReader_ab (kids_blkR kids cap ++ keys_blkR ty keys cap))).
assert (HWINx : fwin_x SEGS ly W regs mem e)
  by (split; [exact He0|]; split; [exact He16|]; split; [exact Hetop | exact Hepres]).
pose proof (ajournal_x_init_WR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (@STK_grow prh_img_A) e FP
  ly S Hp W regs mem md ch HPREX HWINx) as HJ.
remember (Eimg (Ereg regs (grow_extra ty kids keys n cap))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
pose proof HH as ((_ & HRW) & (Hty & Vty) & _ & _ & (Hkids & Vkids) & (Hkeys & Vkeys) & (Hn & Vn) & (Hcap & Vcap)).
assert (EXn : forall j, (j < 7)%nat -> ew E (32 + j) = nth j (grow_extra ty kids keys n cap) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
pose proof (EXn 4%nat ltac:(lia)) as E36. pose proof (EXn 5%nat ltac:(lia)) as E37.
pose proof (EXn 2%nat ltac:(lia)) as E34. pose proof (EXn 3%nat ltac:(lia)) as E35.
pose proof (EXn 6%nat ltac:(lia)) as E38.
cbn [Nat.add nth grow_extra] in E34, E35, E36, E37, E38.
assert (D34 : sv_denot E (SOff 34 0) = Z_to_bv 64 kids)
  by (cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D35 : sv_denot E (SOff 35 0) = Z_to_bv 64 keys)
  by (cbn [sv_denot]; rewrite E35, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D36 : sv_denot E (SOff 36 0) = Z_to_bv 64 n)
  by (cbn [sv_denot]; rewrite E36, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (D37 : sv_denot E (SOff 37 0) = Z_to_bv 64 cap)
  by (cbn [sv_denot]; rewrite E37, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
assert (U2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (U10 : bv_unsigned (ew E 10) = v).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
  unfold w64. apply unsigned_lit_small. lia. }
unfold fpostWmR, fpostWR. unfold cfg_at. rewrite grow_ent.
(* THE m-FORM KEEP (fQmn): P := `memnorm mem -> memnorm m` is an invariant of the runs (srr_inv_laws_imp over
   srr_inv_laws_memnorm_k) and of each realloc call (srr_inv_call_imp: the callee's own m-form keep); it holds at
   entry, and at each ret it IS the keep. Opaque inside the walk, so no engine computation meets memnorm. *)
set (PM := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
assert (PLAW : srr_inv_laws SEGS PM)
  by exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)).
assert (PCALL : srr_inv_call SEGS PM) by exact (srr_inv_call_imp SEGS mem).
assert (PEND : forall m, PM m -> YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m) by (intros m Hm; exact Hm).
assert (HPM : PM mem) by (intros Hm; exact Hm).
clearbody PM.
paj_run_tok_x_inv (RUNP PM PLAW) HS HJ SHOK HPM grow_Bspan.
- apply grow_awr_ok_fr with (v := v) (FR := 80);
    [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
- (* the first stretch: the kept relation, the frame and the growth from entry *)
  pose proof (proj1 HJ) as HAR1.
  assert (FS128 : 128 <= @STK_grow prh_img_A) by (apply Z.leb_le; vm_compute; reflexivity).
  pose proof (cj_kept_reflR (SK := SK) SEGS B PST ARx (wle' SEGS RZ_cf) (wle'_refl SEGS RZ_cf) (@STK_grow prh_img_A) (spZ regs) (grow_OR v) FP ly S W mem md) as HKEPT0.
  destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E (ss_mem ss_grow0) W mem mem md (ms_mem ms)
    (with_vm_backing (m_vm_lazy md) mat md) (spZ regs) v FP ly S Hp W mem md ly S Hp
    ltac:(lia) FS HKEPT0 (fun _ _ => eq_refl) (fun _ H => H) HAR HAR Hceil Hslo Hshi HFr HG
    ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any md mat)) as (HKEPT1 & F1 & G1).
  psrr_branch_tok RUN BR HS SHOK grow_Bspan.
  + (* n = cap: grow the arrays *)
    assert (Heq : n = cap).
    { rewrite D36, D37 in Hc. cbn [branch_taken] in Hc. unfold bv_ltu in Hc.
      rewrite !unsigned_lit_small in Hc by lia.
      apply negb_true_iff in Hc. apply Z.ltb_ge in Hc. destruct HSLOT as (_ & Hnc & _). lia. }
    paj_run_tok_x_inv (RUNP PM PLAW) HS HJ SHOK HPM grow_Bspan.
    * apply grow_awr_ok_fr with (v := v) (FR := 80);
        [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
    * pose proof (proj1 HJ) as HAR2.
      destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E _ W mem (ms_mem ms)
        (with_vm_backing (m_vm_lazy md) mat md) (ms_mem ms0) _ (spZ regs) v FP ly S Hp W mem md ly S Hp
        ltac:(lia) FS HKEPT1 F1 G1 HAR HAR1 Hceil Hslo Hshi HFr0 HG0
        ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any _ mat0)) as (K2 & F2 & G2).
      psrr_branch_tok RUN BR HS SHOK grow_Bspan.
      -- (* cap <> 0: cap' = 2 cap *)
         paj_run_to_tok_x_inv (RUNTOP PM PLAW) HS HJ SHOK HPM grow_Bspan (GROW_OFF + 136).
         ++ apply grow_awr_ok_fr with (v := v) (FR := 80);
              [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
         ++ (* the kids call: A 0x86a68, a0 = kids, a1 = 56 * cap2R cap *)
            pose proof (proj1 HJ) as HARc.
            destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E _ W mem (ms_mem ms0)
              (with_vm_backing (m_vm_lazy md) mat0 md) (ms_mem ms1) _ (spZ regs) v FP ly S Hp W mem md ly S Hp
              ltac:(lia) FS K2 F2 G2 HAR HAR2 Hceil Hslo Hshi HFr1 HG1
              ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any _ mat1)) as (K3 & F3 & G3).
            assert (Hc0' : cap <> 0).
            { lazymatch goal with Hb : branch_taken BC_NE _ _ = true |- _ =>
                rewrite branch_ne_U in Hb; rewrite (U_atom E 37 cap E37) in Hb by lia;
                rewrite (U_lit E 0) in Hb by lia; intros Hz; rewrite Hz in Hb; cbn in Hb; discriminate Hb end. }
            assert (P6 : sv_denot E (SOff 38 0) = sv_denot E (SAlu ALU_SLL (SOff 37 0) (SLit 1))).
            { destruct HSLOT as (_ & Hnc & _).
              apply U_inj. rewrite U_SAlu, U_SLit, (U_atom E 37 cap E37) by lia.
              rewrite (U_atom E 38 (cap2R cap) E38)
                by (unfold cap2R; rewrite (proj2 (Z.eqb_neq cap 0) Hc0'); lia).
              cbn [zalu_raw]. change (Z.land (zcanon 1) 63) with 1. rewrite Z.shiftl_mul_pow2 by lia.
              unfold cap2R. rewrite (proj2 (Z.eqb_neq cap 0) Hc0'). change (2 ^ 1) with 2.
              unfold zcanon, M64. rewrite Z.mod_small; lia. }
            norm_ss HS. apply st_ok_pi_drop_cond in HS.
            pose proof (st_ok_pi_pin E _ _ 22%bv (SOff 38 0) HS P6) as HSJ. clear HS.
            lazymatch type of HSJ with st_ok_pi _ _ _ ?s _ =>
              replace s with ss_grow_J in HSJ by (vm_compute; reflexivity) end.
            subst E.
            exact (grow_from_J CTX0 D ms1 _ PM PLAW PCALL PEND HPD Heq HPM HSJ SHOK HJ K3 F3 G3).
      -- (* cap = 0: cap' = 8 *)
         paj_run_to_tok_x_inv (RUNTOP PM PLAW) HS HJ SHOK HPM grow_Bspan (GROW_OFF + 136).
         ++ apply grow_awr_ok_fr with (v := v) (FR := 80);
              [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
         ++ pose proof (proj1 HJ) as HARc.
            destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E _ W mem (ms_mem ms0)
              (with_vm_backing (m_vm_lazy md) mat0 md) (ms_mem ms1) _ (spZ regs) v FP ly S Hp W mem md ly S Hp
              ltac:(lia) FS K2 F2 G2 HAR HAR2 Hceil Hslo Hshi HFr1 HG1
              ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any _ mat1)) as (K3 & F3 & G3).
            assert (Hcz : cap = 0).
            { lazymatch goal with Hb : branch_taken BC_NE _ _ = false |- _ =>
                rewrite branch_ne_U in Hb; rewrite (U_atom E 37 cap E37) in Hb by lia;
                rewrite (U_lit E 0) in Hb by lia; apply negb_false_iff in Hb; apply Z.eqb_eq in Hb; exact Hb end. }
            assert (P6 : sv_denot E (SOff 38 0) = sv_denot E (SLit 8)).
            { apply U_inj. rewrite (U_lit E 8) by lia.
              rewrite (U_atom E 38 (cap2R cap) E38); [rewrite Hcz; reflexivity | rewrite Hcz; cbn; lia]. }
            norm_ss HS. apply st_ok_pi_drop_cond in HS.
            pose proof (st_ok_pi_pin E _ _ 22%bv (SOff 38 0) HS P6) as HSJ. clear HS.
            lazymatch type of HSJ with st_ok_pi _ _ _ ?s _ =>
              replace s with ss_grow_J in HSJ by (vm_compute; reflexivity) end.
            subst E.
            exact (grow_from_J CTX0 D ms1 _ PM PLAW PCALL PEND HPD Heq HPM HSJ SHOK HJ K3 F3 G3).
  + (* n < cap: nothing to do, return 0 *)
    assert (Hlt : n < cap).
    { rewrite D36, D37 in Hc. cbn [branch_taken] in Hc. unfold bv_ltu in Hc.
      rewrite !unsigned_lit_small in Hc by lia.
      apply negb_false_iff in Hc. apply Z.ltb_lt in Hc. exact Hc. }
    paj_run_tok_x_inv (RUNP PM PLAW) HS HJ SHOK HPM grow_Bspan.
    * apply grow_awr_ok_fr with (v := v) (FR := 80);
        [lia | exact FS | exact He0 | grow_wr U2 U10 | apply grow_FP_v | exact Hvloc].
    * destruct (grow_stretch B ARx SK LAWS (@STK_grow prh_img_A) 80 E _ W mem (ms_mem ms)
        (with_vm_backing (m_vm_lazy md) mat md) (ms_mem ms0) _ (spZ regs) v FP ly S Hp W mem md ly S Hp
        ltac:(lia) FS HKEPT1 F1 G1 HAR HAR1 Hceil Hslo Hshi HFr0 HG0
        ltac:(grow_wr_tac U2 U10) (same_but_materialized_wvb_any _ mat0)) as (K2 & F2 & G2).
      eapply (grow_ret B ARx SK LAWS PL_grow (@STK_grow prh_img_A) W E _ ms0 _ e FP regs (grow_extra ty kids keys n cap)
        ly S Hp W mem md (grow_OR v) FP ly S Hp _ _ ltac:(lia) HS eq_refl ltac:(vm_compute; reflexivity));
        [ subst E; apply agree_Ereg; apply env_agree_refl
        | vm_compute; reflexivity
        | reflexivity
        | exact Hra
        | exact HJ
        | exact K2
        | intros a (r & Hr & Ha); exists r; split; [apply in_or_app; left; exact Hr | exact Ha]
        | ].
      intros mat'. unfold fQmn. split; [|exact (PEND _ HPM)]. cbv beta.
      assert (Hsp128 : YM05.alloc_ceiling + 128 <= spZ regs) by lia.
      assert (Hv0' : 0 <= v) by lia. assert (Hv64 : v + 56 <= 2 ^ 64) by lia. assert (Hc0 : 0 <= cap) by lia.
      split; [exact HROOM|].
      split; [apply PresetHullBudget.hull_used_refl|].
      split.
      { assert (Hg : PRH_Charge.prhPg_gtrace (ty =? 6) n cap = []).
        { unfold PRH_Charge.prhPg_gtrace, PjGrammar.grow.
          rewrite (proj2 (Nat.ltb_lt (Z.to_nat n) (Z.to_nat cap))) by lia. reflexivity. }
        rewrite Hg. unfold PRH_Charge.prh_held. cbn [PjGrammar.held PjGrammar.calls]. lia. }
      left.
      split; [exact Hlt|].
      split; [prreg HS (10%bv : bv 5) R10; cbn [ms_regs restrict] in R10; rewrite R10; reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split; [reflexivity|].
      split.
      { eapply prh_ledger_keep; [exact HLED|]. intros a Hca.
        destruct (grow_cell_apart B ARx LAWS pst_img 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v a
          ltac:(lia) HAR HLED HAT Hsp128 Hoff Hca) as (Ha64 & Hnw).
        apply F2. rewrite unsigned_lit_small by lia. exact Hnw. }
      split.
      { (* the written fields still hold their entry values: this arm stores nothing *)
        pose proof (st_ok_region_nth SEGS E _ _ 1 grow_vA HS ltac:(vm_compute; reflexivity)) as RA.
        pose proof (st_ok_region_nth SEGS E _ _ 2 grow_vB HS ltac:(vm_compute; reflexivity)) as RB.
        cbn [ms_mem restrict] in RA, RB.
        assert (Vk : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 24) (N.to_nat 8) kids).
        { eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 24 8%N (SOff 34 0) kids RA U10);
            [cbn; tauto | exact D34 | cbn; lia | cbn; lia]. }
        assert (Vy : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 32) (N.to_nat 8) keys).
        { eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 32 8%N (SOff 35 0) keys RA U10);
            [cbn; tauto | exact D35 | cbn; lia | cbn; lia]. }
        assert (Vc : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (v + 48) (N.to_nat 8) cap).
        { eapply (field_of_region SEGS E _ 10 v _ _ _ _ _ 48 8%N (SOff 37 0) cap RB U10);
            [cbn; tauto | exact D37 | cbn; lia | cbn; lia]. }
        apply (grow_hdr_keep 80 (w_H W) mem (ms_mem ms0) (spZ regs) v ty num str kids keys n cap kids keys cap
          HH F2 G2 Hvstk Hv0' Hv64); [split; [exact Hkids | exact Vk] | split; [exact Hkeys | exact Vy]
          | split; [exact Hcap | exact Vc]]. }
      split.
      { (* the slot blocks: untouched *)
        intros lo hi x Hlh Hx.
        destruct (grow_slot_apart B ARx LAWS 80 ly S Hp W mem md Lam peak cnt fail ran most own regs e v ty kids keys n cap lo hi x
          ltac:(lia) Hc0 HAR HLED HAT Hsp128 HSLOT HAP Hlh Hx) as (Hx64 & Hnw).
        apply aview_eq_of. apply F2. rewrite unsigned_lit_small by lia. exact Hnw. }
      (* no allocator call (outcomes []): E = [] at n < cap, the live requests and the position kept *)
      rewrite (grow_evs_lt _ _ _ _ Hlt). split; [rewrite PresetReqAt.hlive_from_nil; apply Permutation_refl|].
      intros sm x os i H0 hist Hpos _. exists hist. cbn [length]. rewrite Nat.add_0_r. exact Hpos.
Qed.

(* THE PER-RECORD FORM IS THE KIT'S TEXT, record by record: the restated tgrow_specX (lib/A/PRH_FnReader.v) is exactly
   gr_pre at every record giving the conclusion at that record, so grow_K0_of_args states the text at ONE record.
   Machine-checked here, so gr_pre / gr_Q cannot drift from the text. *)
Lemma tgrow_specX_records : forall CTX0, tgrow_specX B ARx SK CTX0 <->
  (forall D : gr_in, gr_pre CTX0 D ->
     SRr' SEGS RZ_cf (gi_W D) (cfg_at SEGS (@pa_sigma _ A_prog_listing PI_prog_A AS_grow) (gi_regs D) (gi_mem D)
       (gi_md D)) (gr_post D)).
Proof.
intros CTX0. split.
- intros H D HPD. destruct D as [ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own].
  unfold gr_pre in HPD. cbn [gi_ly gi_S gi_Hp gi_W gi_regs gi_mem gi_md gi_ch gi_e gi_v gi_ty gi_num gi_str gi_kids gi_keys gi_n gi_cap
  gi_kb gi_yb gi_Lam gi_peak gi_cnt gi_fail gi_ran gi_most gi_own] in HPD.
  destruct HPD as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18
    & H19 & H20).
  exact (H most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb
    yb Lam peak cnt fail ran H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20).
- intros H. unfold tgrow_specX.
  intros most own ly S Hp W regs mem md ch e v ty num str kids keys n cap kb
    yb Lam peak cnt fail ran H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20.
  exact (H (mkGrIn ly S Hp W regs mem md ch e v ty num str kids keys n cap kb yb Lam peak cnt fail ran most own)
    (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
      (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 H20)))))))))))))))))))).
Qed.

(* THE WHOLE FUNCTION (rule-24 CONFIRM for grow in hand on both images, telemetry 2026-10-30 00:40Z): the kit's tgrow_specX
   EXACTLY (PRH_FnReader.v f1ae32e3b2cd at 7cdbb61b5fa0), from the per-record walk and the record form above; a caller
   that names `tgrow_specX B ARx SK CTX0` as a hypothesis closes it by citing this *)
Theorem grow_holds : forall CTX0, tgrow_specX B ARx SK CTX0.
Proof. intros CTX0. apply (proj2 (tgrow_specX_records CTX0)). exact (grow_K0_of_args CTX0). Qed.


End c.

(* ---- THE IMAGE WITNESSES OF THE SECTION'S STAND-INS (A', #102): TL := PALibA.palib_A (lib/A/PALibA.v blob
   88c72c8175cf, the cut's), B := AD2l.TfibB. LAWS at two allocator relations: PALibA's own ARcf (palib_laws_A), and the
   placed one ARcf /\ xs_placed_cf (YGcallcf's ARxs; LAWS by YGcallcf.AR_laws_x_xs over YG0lawscf.AR_laws_ok_cf),
   which is the relation the parse_value A' top names (VrdTop.v vt_ARA). HREALLOC (tfuzz_realloc_specX, owner
   the allocator lane's S1 walk of fuzz_realloc) stays a premise. ---- *)
Section inst. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Existing Instance prh_img_A.
#[local] Existing Instance CfParamsPreset.CfParams_preset.
#[local] Abbreviation CP := CfParamsPreset.CfParams_preset.
#[local] Abbreviation TA := AD2l.TfibB.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation ARI := (YG0ncf.ARcf (cp := CP) SEGS TA).
#[local] Abbreviation ARXS :=
  (fun ly S Hp (W : world SEGS) mem md => YG0ncf.ARcf (cp := CP) SEGS TA ly S Hp W mem md /\ YG0ncf.xs_placed_cf ly S).
(* GUARD (CrcBp's wrong-image trap, owner 19:3xZ): the segments the walk and the PALibA witnesses state over are the
   A' asan image's, by reflexivity on FULLY QUALIFIED names (a short `Img0.rsegs` can resolve to the plain image) *)
Lemma grow_segs_Aprime : SEGS = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs /\
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs =
  OSSVerify.omx_clap_core.fuzz_preset.images.Asan.M.loaded_segments.
Proof. split; reflexivity. Qed.
Lemma grow_laws_xs_Aprime : AR_laws_x SEGS TA ARXS (@cf_head CP).
Proof. exact (YGcallcf.AR_laws_x_xs SEGS TA (YG0lawscf.AR_laws_ok_cf SEGS TA)). Qed.
Theorem grow_K0_of_args_Aprime : forall SK (HREALLOC : tfuzz_realloc_specX (cp := CP) TA ARI SK) CTX0 D,
  gr_pre (cp := CP) TA ARI CTX0 D ->
  SRr' SEGS RZ_cf (gi_W D) (cfg_at SEGS (@pa_sigma _ A_prog_listing PI_prog_A AS_grow) (gi_regs D) (gi_mem D) (gi_md D))
    (gr_post (cp := CP) TA ARI SK D).
Proof.
intros SK HREALLOC.
exact (grow_K0_of_args (cp := CP) TA ARI SK PALibA.palib_laws_A PALibA.palib_A HREALLOC).
Qed.
(* the name is an earlier round's; the theorem states the kit's text itself *)
Theorem grow_draft_Aprime : forall SK (HREALLOC : tfuzz_realloc_specX (cp := CP) TA ARI SK) CTX0,
  tgrow_specX (cp := CP) TA ARI SK CTX0.
Proof.
intros SK HREALLOC CTX0.
exact (grow_holds (cp := CP) TA ARI SK PALibA.palib_laws_A PALibA.palib_A HREALLOC CTX0).
Qed.
(* THE A' WHOLE-FUNCTION THEOREM at the placed relation (the parse_value A' top's H_grow, VrdTop.v, at RL := prh_room_live_a8
   CP and every float state, closes by citing this with its own HREALLOC) *)
Theorem grow_holds_Aprime : forall SK (HREALLOC : tfuzz_realloc_specX (cp := CP) TA ARXS SK) CTX0,
  tgrow_specX (cp := CP) TA ARXS SK CTX0.
Proof.
intros SK HREALLOC CTX0.
exact (grow_holds (cp := CP) TA ARXS SK grow_laws_xs_Aprime PALibA.palib_A HREALLOC CTX0).
Qed.
End inst.


Print Assumptions grow_K0_of_args.
Print Assumptions tgrow_specX_records.
Print Assumptions grow_K0_of_args_Aprime.
Print Assumptions grow_draft_Aprime.
Print Assumptions grow_holds.
Print Assumptions grow_holds_Aprime.
(* THE WRONG-IMAGE CHECK (rebind rule 7): every PA / L / PI argument of the A' tops names image A' *)
Set Printing Implicit. Unset Printing Notations.
About grow_holds_Aprime.
About grow_draft_Aprime.
About grow_K0_of_args_Aprime.
