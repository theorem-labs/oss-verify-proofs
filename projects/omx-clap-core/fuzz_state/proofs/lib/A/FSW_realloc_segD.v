(* proves function fuzz_realloc, segment SEG-D (A 0x829e8), as fsr_segD : forall B, fsr_segD_stmt B against a Theorem Labs lane's frozen FSW_realloc_pn.v (reuse search: ossv proof index v5, built 2026-10-29T04:26:29Z from main@f4cc67298b7 ossv/recipes@e5e7eba2cc0 ossv/candidates@ee89628c997 release/pau-projects-recipes@b6a0088adcb, every branch is where the index read it / `proof-index fuzz_realloc 0x82ba8 0x82bbc 0x82c74 0x82b34 0x54894`, exit 1: none for the ASan image; two named working branches: none; CONFIRM x2, (internal path)) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YM05 YG00 YG0a YG01 YG0l YG0d YG0f YG0n YG05 YG08 YG0q YCbq YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w AB13 FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_ReallocModel
FSupoisonRealloc FSpoisonS FSW_K FSW_ret FSW_rres FSW_statics FSW_statics_awr FSW_head FSW_poison_conv FSW_K3
FSW_fuzz_realloc_tbl FSW_realloc FSW_realloc_pn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The resume state at FSR_RA_POISON (0x82ba8): FSW_ret's fss_retT with the frame's eight saved words as chunks over   *)
(* the extra atoms xatom 4..11 (the entry's s6 s5 s4 s3 s2 s1 s0 ra, FSW_K's atom convention: the saved-register      *)
(* chunks take the atoms after the walk's xs = the statics), the four static regions, and s3 pinned to its value.     *)
(* ---------------------------------------------------------------------------------------------------------------- *)

Definition FSRD_CS : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 8 (SOff 37 0)); YP09.mkChunk 8 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0));
   YP09.mkChunk 24 (CVal 8 (SOff 40 0)); YP09.mkChunk 32 (CVal 8 (SOff 41 0)); YP09.mkChunk 40 (CVal 8 (SOff 42 0));
   YP09.mkChunk 48 (CVal 8 (SOff 43 0)); YP09.mkChunk 56 (CVal 8 (SOff 44 0))].
(* the entry's callee-saved words in the frame's order (fsr_frame_vals: sp0 - 64 .. sp0 - 8) *)
Definition fsrD_saved (regs : bvmap 5 word) : list word :=
  [YK11.getr regs 22; YK11.getr regs 21; YK11.getr regs 20; YK11.getr regs 19; YK11.getr regs 18; YK11.getr regs 9;
   YK11.getr regs 8; YK11.getr regs 1].
Definition fsrD_ss0 : sstate :=
  let s := fss_retT FSR_RA_POISON 64 FSRD_CS fs_pstat_regions [] in
  mkSS (ss_pc s) (sr_set (ss_regs s) 19%bv (SLit FSR_S3)) (ss_mem s) (ss_resv s) (ss_facts s).

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

(* a register set to an expression of its value *)
Lemma fsrD_pin : forall E ss (H : word -> bool) regs pc mem rom (r : bv 5) e,
  st_ok tfibsegs E ss (restrict H (mkst regs pc mem rom)) -> bv_eqb r 0 = false -> sv_denot E e = YK11.getr regs r ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss))
    (restrict H (mkst regs pc mem rom)).
Proof.
intros E ss H regs pc mem rom r e HS Hr He.
apply (st_ok_regs tfibsegs E ss _ (sr_set (ss_regs ss) r e)); [exact HS|].
intros x. destruct (base.decide (x = r)) as [->|Hne].
- rewrite (sr_get_set_same _ r e Hr), He. exact (st_ok_reg tfibsegs E ss _ r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* a frame chunk over an extra atom holding the saved word *)
Lemma fsrD_chunk : forall E m base off (j : nat) (w : word), ew E j = w ->
  val_mem tfibsegs m (base + off) 8 (bv_unsigned w) ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 (SOff j 0))).
Proof.
intros E m base off j w Hw Hv.
apply (chunk_ok_val tfibsegs E m base off 8 (SOff j 0) (bv_unsigned w)).
- rewrite fsw_SOff0, Hw. symmetry. apply Z_to_bv_bv_unsigned.
- replace (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64) by reflexivity. apply bv_unsigned_in_range.
- cbn. lia.
- exact Hv.
Qed.

(* the four static regions under an env whose xatom 0..3 are fs_glob's values, followed by any further atoms *)
Lemma fsrD_pstat_ok : forall (W : world tfibsegs) regs mem live peak cnt fail extra,
  fs_glob tfibsegs W mem live peak cnt fail ->
  Forall (region_ok tfibsegs (Ereg regs (fs_extraT ++ fs_pstat_xs cnt fail live peak ++ extra)) (mrestrict (w_H W) mem))
    fs_pstat_regions.
Proof.
intros W regs mem live peak cnt fail extra GL.
pose proof GL as (G1 & G2 & G3 & G4 & GR).
set (E := Ereg regs (fs_extraT ++ fs_pstat_xs cnt fail live peak ++ extra)).
assert (RS : forall g (j : nat) v, ew E (32 + j) = Z_to_bv 64 v ->
  0 <= v < 2 ^ 64 -> 0x9f000 <= g -> g + 8 <= 0x5fd000 -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) (fs_pstat_region g (32 + j))).
{ intros g j v Hv Hr Hg1 Hg2 Hm.
  unfold region_ok, fs_pstat_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. unfold writable_at. apply AB13.tfib_rw_window. rewrite unsigned_lit_small by lia. lia.
  - constructor; [|constructor].
    exact (chunk_ok_val tfibsegs _ _ 0 g 8 (SOff (32 + j) 0) v
      ltac:(rewrite fsw_SOff0; exact Hv) ltac:(cbn [Z.of_N]; lia)
      ltac:(cbn [Z.of_N]; lia) ltac:(cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Hm)). }
unfold fs_pstat_regions, xatom.
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
- apply (RS G_COUNT 1%nat cnt); [subst E; rewrite ew_Ereg_extra; reflexivity | lia | unfold G_COUNT; lia
  | unfold G_COUNT; lia | exact G3].
- apply (RS G_FAIL 2%nat fail); [subst E; rewrite ew_Ereg_extra; reflexivity | lia | unfold G_FAIL; lia
  | unfold G_FAIL; lia | exact G4].
- apply (RS G_LIVE 3%nat live); [subst E; rewrite ew_Ereg_extra; reflexivity | lia | unfold G_LIVE; lia
  | unfold G_LIVE; lia | exact G1].
- apply (RS G_PEAK 4%nat peak); [subst E; rewrite ew_Ereg_extra; reflexivity | lia | unfold G_PEAK; lia
  | unfold G_PEAK; lia | exact G2].
Qed.

(* the resume regions are pairwise disjoint: the frame lies above every image cell *)
Lemma fsrD_pd : forall E sp0, bv_unsigned (ew E 2) = sp0 - 64 -> 0x600000 + 64 <= sp0 ->
  pairwise_disjoint E (fsT_ret_regions 64 FSRD_CS fs_pstat_regions).
Proof.
intros E sp0 E2 H1.
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fs_pstat_regions, fs_got_region, fs_bcell_region, fstk_ret, fs_pstat_region, extent_of_region.
cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
  G_COUNT, G_FAIL, G_LIVE, G_PEAK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
Qed.

(* a byte below the frame and off the image is in no write window of a state shaped as the resume state *)
Lemma fsrD_nwr : forall E rs a, skeleton rs = skeleton (fsT_ret_regions 64 FSRD_CS fs_pstat_regions) ->
  a < bv_unsigned (ew E 2) -> ~ in_img tfibsegs a -> ~ in_wrange E rs a.
Proof.
intros E rs a Hsk Ha Hi Hw.
apply (in_wrange_skeleton E rs _ a Hsk) in Hw.
destruct Hw as (r & Hr & Hra).
unfold fsT_ret_regions, fs_pstat_regions in Hr. cbn [app] in Hr.
repeat (destruct Hr as [<- | Hr]).
all: first
  [ solve [exact Hr]
  | solve [cbn [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; lia]
  | solve [cbn [fs_got_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; lia]
  | solve [cbn [fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; lia]
  | solve [cbn [fs_pstat_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra; apply Hi, fs_pstat_img;
           first
             [ apply (inFP_FS_PSTAT_FP G_COUNT); [vm_compute; tauto | lia]
             | apply (inFP_FS_PSTAT_FP G_FAIL); [vm_compute; tauto | lia]
             | apply (inFP_FS_PSTAT_FP G_LIVE); [vm_compute; tauto | lia]
             | apply (inFP_FS_PSTAT_FP G_PEAK); [vm_compute; tauto | lia] ] ] ].
Qed.

(* a run's frame keeps a byte outside its write windows *)
Lemma fsrD_mbyte_frame : forall E rs (m m' : word -> option byte) a, frame_of E rs m m' -> 0 <= a < 2 ^ 64 ->
  ~ in_wrange E rs a -> mbyte tfibsegs m' a = mbyte tfibsegs m a.
Proof.
intros E rs m m' a HF Ha Hn. unfold mbyte. rewrite HF; [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma fsrD_val_mem_keep : forall (m m' : word -> option byte) a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v K H j Hj. rewrite K by lia. exact (H j Hj). Qed.

Lemma fsrD_garr8_keep : forall (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> mbyte tfibsegs m' x = mbyte tfibsegs m x) ->
  garr8 tfibsegs m a l -> garr8 tfibsegs m' a l.
Proof.
intros m m' a l K H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (fsrD_val_mem_keep m m' (a + Z.of_nat j) 1 _); [intros x Hx; apply K; lia | exact Hv].
Qed.

(* a callee-saved register the walk never wrote, read after a call that preserved it *)
Lemma fsrD_kept_reg : forall regs regs3 regsT extra (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r ->
  acallee_saved (bv_unsigned r) -> aregs_preserved regsT regs3 -> YK11.getr regsT r = YK11.getr regs r ->
  sv_denot (Ereg regs3 extra) (SOff n 0) = YK11.getr regs r.
Proof.
intros regs regs3 regsT extra r n Hn Hc HP Hr.
rewrite fsw_SOff0, (ew_Ereg_nat regs3 extra n r Hn), (fsw_pres regsT regs3 r HP Hc). exact Hr.
Qed.

(* the result witness of a post stated with an existential *)
Lemma fsrD_ex : forall (W : world tfibsegs) c (P : Z -> world tfibsegs -> config -> Prop) r,
  SRr tfibsegs W c (P r) -> SRr tfibsegs W c (fun W' c' => exists res, P res W' c').
Proof. intros W c P r H. eapply SRr_mono; [exact H|]. intros W' c' _ HP. exists r. exact HP. Qed.

Variable B : asyms.

(* a byte that is no shadow byte reads the same raw as unpoisoned, at both ends of a call *)
Lemma fsrD_low_keep : forall ly S U U' (W : world tfibsegs) mem mem' md md' a,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly S U' W mem' md' -> 0 <= a < 2 ^ 64 ->
  a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a ->
  mbyte tfibsegs (mrestrict (w_H W) mem') a = mbyte tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U U' W mem mem' md md' a H H' Ha Hr Ev.
assert (N1 : in_ush U' (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite unsigned_lit_small by lia. destruct (in_ush U' a) eqn:Ei; [|reflexivity].
  destruct (ush_facts tfibsegs B ly S U' W mem' md' a H' Ei) as (_ & L1 & L2). lia. }
assert (N0 : in_ush U (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite unsigned_lit_small by lia. destruct (in_ush U a) eqn:Ei; [|reflexivity].
  destruct (ush_facts tfibsegs B ly S U W mem md a H Ei) as (_ & L1 & L2). lia. }
eapply fsw_mbyte_of_aview.
rewrite <- (aview_unpoison_out tfibsegs (w_H W) U' mem' a N1), <- (aview_unpoison_out tfibsegs (w_H W) U mem a N0).
exact Ev.
Qed.

Hypothesis IMG : fs_img_facts tfibsegs B.

(* R2 for every run of this segment: a state shaped as the resume state *)
Lemma fsrD_awr : forall E rs STK sp0 FP bl0 blc ly own fr0,
  bv_unsigned (ew E 2) = sp0 - 64 -> 64 <= STK -> (forall a, inFP FS_PSTAT_FP a -> inFP FP a) ->
  skeleton rs = skeleton (fsT_ret_regions 64 FSRD_CS fs_pstat_regions) ->
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E rs STK sp0 FP bl0 blc ly own fr0 E2 HS HFP Hsk.
exact (fsr_awr_skel B E _ rs STK sp0 FP bl0 blc ly own fr0
  (fsw_awr_retTS B IMG E FSR_RA_POISON 64 STK sp0 FSRD_CS [] FP bl0 blc ly own fr0 E2 ltac:(lia) HFP) Hsk).
Qed.
End h.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.

Theorem fsr_segD : forall B, fsr_segD_stmt B.
Proof.
intros B PO IMG FS_GOT FS_CELL ly S U W regs mem md ch p k n old live peak cnt fail U1 U2 W2 c HPRE HAT.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HPRE as (HFP & FH & H10 & H11 & Hn1 & HnM & HGL & Hlive & Hcnt & Hcf & Hp0 & EU & HRB & Hlen & HZB & Hkl
  & Hev & Hbb).
destruct HAT as (ly2 & S2 & regsT & memT & md2 & b & b1 & b2 & -> & HJ & HARU & Eab & Eab2 & OK & FH2 & Ha0 & Ha1
  & Hra & Hsp & Hs0 & Hs2 & Hs3 & HK & HFV & HGL2 & HV & HZ).
pose proof HFP as (HAP & _).
pose proof HAP as (HAN & _ & _).
pose proof HAN as (_ & Hra0 & _ & Hgp0 & Htp0 & _).
pose proof (fsw_sp B STK_fuzz_realloc ly S U W regs mem md ch HAP) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (FR : STK_fuzz_realloc = 18656) by reflexivity.
pose proof HK as (HK1 & HKgp & HKtp).
pose proof HGL as (G1 & G2 & G3 & G4 & GR).
(* the new block (b, n + HEAD) *)
assert (Hin : In (b, n + HEAD) (ablocks B ly2 S2)) by (rewrite Eab2; apply in_or_app; right; left; reflexivity).
pose proof HARU as (HAR2 & _ & _).
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 b (n + HEAD) HAR2 Hin) as (Hb16 & Hb4096 & Hbceil & Happ & _ & _ & _).
assert (Hreq : req_size (n + HEAD) = n + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (n + 16) 0); lia).
rewrite Hreq in Hbceil, Happ.
(* own's poison call (b, 16): the head joins U at the end *)
eapply SRr_bind.
{ exact (fsw_poison16_atU B PC_poison PO STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W (unpoison U mem) md [] ly2 S2
    (U1 ++ U2) (U1 ++ U2 ++ [(b + HEAD - HEAD, HEAD)]) W2 memT md2 3 regsT (-64) b b (n + HEAD)
    HJ HARU ltac:(lia) eq_refl ltac:(lia) ltac:(rewrite FR; unfold ESTACK; lia)
    ltac:(unfold YK0s.ret_ok; rewrite Hra; apply bv_eq; vm_compute; reflexivity)
    HKgp HKtp Ha0 Ha1 OK
    ltac:(replace (b + HEAD - HEAD) with b by lia; rewrite app_assoc; apply Permutation_cons_append)
    Hin ltac:(lia) ltac:(rewrite Hreq; unfold HEAD; lia)). }
cbv beta. intros W' c' _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HARU3 & HP3 & Hkeep & Hfr).
rewrite Hra.
(* the resume state at 0x82ba8 *)
set (xs := fs_pstat_xs (cnt + 1) fail (live - k) peak ++ fsrD_saved regs).
set (E := Ereg regs3 (fs_extraT ++ xs)).
assert (Esp3 : YK11.getr regs3 2 = YK11.getr regsT 2) by exact (HP3 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 64).
{ subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Esp3. exact Hsp. }
assert (GL3 : fs_glob tfibsegs W2 mem3 (live - k) peak (cnt + 1) fail).
{ pose proof HGL2 as (L1 & L2 & L3 & L4 & LR).
  assert (KS : forall g, 0x9f000 <= g -> g + 8 <= 0x5fd000 -> forall v,
    val_mem tfibsegs (mrestrict (w_H W2) memT) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) mem3) g 8 v).
  { intros g Hg1 Hg2 v Hv. apply (fsrD_val_mem_keep (mrestrict (w_H W2) memT) (mrestrict (w_H W2) mem3) g 8 v);
      [|exact Hv].
    intros x Hx. apply (fsrD_low_keep B ly2 S2 (U1 ++ U2) _ W2 memT mem3 md2 md3 x HARU HARU3);
      [lia | left; unfold SHADOW_OFF; lia | apply Hfr; [lia | unfold PO_WIN; lia]]. }
  split; [exact (KS G_LIVE ltac:(unfold G_LIVE; lia) ltac:(unfold G_LIVE; lia) _ L1)|].
  split; [exact (KS G_PEAK ltac:(unfold G_PEAK; lia) ltac:(unfold G_PEAK; lia) _ L2)|].
  split; [exact (KS G_COUNT ltac:(unfold G_COUNT; lia) ltac:(unfold G_COUNT; lia) _ L3)|].
  split; [exact (KS G_FAIL ltac:(unfold G_FAIL; lia) ltac:(unfold G_FAIL; lia) _ L4)|].
  exact LR. }
assert (HCS : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) memT) (spZ regs - 64)) FSRD_CS).
{ pose proof HFV as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  unfold FSRD_CS.
  constructor; [apply (fsrD_chunk E _ _ 0 37 (YK11.getr regs 22)); [reflexivity
    | replace (spZ regs - 64 + 0) with (spZ regs - 64) by lia; exact F1]|].
  constructor; [apply (fsrD_chunk E _ _ 8 38 (YK11.getr regs 21)); [reflexivity
    | replace (spZ regs - 64 + 8) with (spZ regs - 56) by lia; exact F2]|].
  constructor; [apply (fsrD_chunk E _ _ 16 39 (YK11.getr regs 20)); [reflexivity
    | replace (spZ regs - 64 + 16) with (spZ regs - 48) by lia; exact F3]|].
  constructor; [apply (fsrD_chunk E _ _ 24 40 (YK11.getr regs 19)); [reflexivity
    | replace (spZ regs - 64 + 24) with (spZ regs - 40) by lia; exact F4]|].
  constructor; [apply (fsrD_chunk E _ _ 32 41 (YK11.getr regs 18)); [reflexivity
    | replace (spZ regs - 64 + 32) with (spZ regs - 32) by lia; exact F5]|].
  constructor; [apply (fsrD_chunk E _ _ 40 42 (YK11.getr regs 9)); [reflexivity
    | replace (spZ regs - 64 + 40) with (spZ regs - 24) by lia; exact F6]|].
  constructor; [apply (fsrD_chunk E _ _ 48 43 (YK11.getr regs 8)); [reflexivity
    | replace (spZ regs - 64 + 48) with (spZ regs - 16) by lia; exact F7]|].
  constructor; [apply (fsrD_chunk E _ _ 56 44 (YK11.getr regs 1)); [reflexivity
    | replace (spZ regs - 64 + 56) with (spZ regs - 8) by lia; exact F8]|].
  constructor. }
assert (HSr : st_ok tfibsegs E (fss_retT FSR_RA_POISON 64 FSRD_CS fs_pstat_regions [])
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 FSR_RA_POISON) mem3 (seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args B STK_fuzz_realloc (spZ regs) (fsr_FPc p k) ly S W (unpoison U mem) md [] ly2 S2
    _ W2 mem3 md3 3 regsT regs3 memT 64 xs FSRD_CS fs_pstat_regions [] FSR_RA_POISON FS_GOT FS_CELL HJ3 HARU3 HP3).
  all: first
    [ solve [exact Hsp]
    | solve [rewrite FR; lia]
    | solve [lazymatch goal with |- _ mod _ = _ => reflexivity end]
    | solve [lazymatch goal with |- regions_wf _ = true => vm_compute; reflexivity end]
    | solve [lazymatch goal with |- Forall (fun _ => _ /\ _) _ => unfold FSRD_CS; repeat constructor; cbn; lia end]
    | solve [exact HCS]
    | solve [intros a Ha; apply Hkeep; lia]
    | solve [exact (fsrD_pstat_ok W2 regs3 mem3 (live - k) peak (cnt + 1) fail (fsrD_saved regs) GL3)]
    | solve [lazymatch goal with |- pairwise_disjoint _ _ => apply (fsrD_pd E (spZ regs) Usp); lia end]
    | solve [exact I]
    | solve [lazymatch goal with |- 0 < _ => reflexivity end] ]. }
assert (E19 : YK11.getr regs3 19 = YK11.getr regsT 19) by exact (HP3 19 ltac:(unfold acallee_saved; lia)).
assert (HS1 : st_ok tfibsegs E fsrD_ss0
  (restrict (w_H W2) (mkst regs3 (Z_to_bv 64 FSR_RA_POISON) mem3 (seg_rom tfibsegs)))).
{ apply (fsrD_pin E _ (w_H W2) regs3 _ mem3 _ 19%bv (SLit FSR_S3) HSr eq_refl).
  rewrite E19, Hs3. apply bv_eq. change (bv_unsigned (sv_denot E (SLit FSR_S3))) with (YP0e.U E (SLit FSR_S3)).
  rewrite U_lit by (unfold FSR_S3; lia). unfold w64. rewrite unsigned_lit_small by (unfold FSR_S3; lia). reflexivity. }
clear HSr.
(* the new block's bytes: below the frame, off the image, and kept by the poison call *)
assert (BLK : forall x, b <= x < b + (n + HEAD) -> 0 <= x < 2 ^ 64 /\ x < spZ regs - 64 /\ ~ in_img tfibsegs x).
{ intros x Hx. split; [lia|]. split; [rewrite FR in Hceil; lia|].
  apply (blk_img _ _ LAWS ly2 S2 W2 _ md2 b (n + HEAD) x HAR2 Hin). rewrite Hreq. exact Hx. }
assert (KB3 : forall x, b <= x < b + (n + HEAD) ->
  mbyte tfibsegs (mrestrict (w_H W2) mem3) x = mbyte tfibsegs (mrestrict (w_H W2) memT) x).
{ intros x Hx. pose proof (in_app_addr b (n + HEAD) x Happ Hx) as Hxa. destruct (BLK x Hx) as (Hx64 & Hxs & _).
  apply (fsrD_low_keep B ly2 S2 (U1 ++ U2) _ W2 memT mem3 md2 md3 x HARU HARU3); [exact Hx64 | |].
  - destruct Hxa as [_ [Hl | [Hh _]]]; [left; unfold kLowShadowBeg, SHADOW_OFF in *; lia | right; exact Hh].
  - apply Hfr; [exact Hx64 | unfold PO_WIN; lia]. }
(* the values the run reads *)
assert (E8 : ew E 8 = Z_to_bv 64 n).
{ assert (E8r : YK11.getr regs3 8 = YK11.getr regsT 8) by exact (HP3 8 ltac:(unfold acallee_saved; lia)).
  subst E. rewrite (ew_Ereg_nat regs3 _ 8 8%bv eq_refl), E8r. exact Hs0. }
assert (E18 : bv_unsigned (ew E 18) = b).
{ assert (E18r : YK11.getr regs3 18 = YK11.getr regsT 18) by exact (HP3 18 ltac:(unfold acallee_saved; lia)).
  subst E. rewrite (ew_Ereg_nat regs3 _ 18 18%bv eq_refl), E18r, Hs2. unfold w64. apply unsigned_lit_small.
  unfold HEAD in Hbceil. lia. }
assert (U8 : YP0e.U E (SOff 8 0) = n) by (apply U_atom; [exact E8 | lia]).
assert (U35 : YP0e.U E (SOff 35 0) = live - k) by (apply U_atom; [reflexivity | lia]).
assert (U36 : YP0e.U E (SOff 36 0) = peak) by (apply U_atom; [reflexivity | lia]).
assert (Usum : YP0e.U E (SAlu ALU_ADD (SOff 8 0) (SOff 35 0)) = live - k + n).
{ rewrite U_SAlu, U8, U35. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
(* 0x82ba8..0x82bb8: g_live += n; stops at the peak branch bgeu 0x82bbc *)
fsw_aj_runU fsr_tbl_ok HS1 HJ3 HARU3.
{ eapply (fsrD_awr B IMG).
  all: first
    [ solve [exact Usp]
    | solve [rewrite FR; lia]
    | solve [exact (fsr_pstat_FPc p k)]
    | solve [lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end] ]. }
assert (KB1 : forall x, b <= x < b + (n + HEAD) ->
  mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) x = mbyte tfibsegs (mrestrict (w_H W2) memT) x).
{ intros x Hx. destruct (BLK x Hx) as (Hx64 & Hxs & Hxi). rewrite <- (KB3 x Hx).
  apply (fsrD_mbyte_frame E _ _ _ x HFr Hx64).
  apply fsrD_nwr; [lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end | rewrite Usp; exact Hxs
  | exact Hxi]. }
clear HF HFr HG KB3.
(* the peak branch: g_peak kept (taken) or set to the new g_live (fall through) *)
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 36 0) (b := SAlu ALU_ADD (SOff 8 0) (SOff 35 0));
  [exact HS1 | intros Hb HS2 | intros Hb HS2].
all: rewrite branch_geu_U, U36, Usum in Hb.
all: revert Hb; destruct (Z.ltb_spec peak (live - k + n)) as [Hpk|Hpk]; intros Hb; cbn in Hb; try discriminate Hb.
(* 0x82bc0 / 0x82bc4 .. 0x82c70: a0 = s2 + 16, the epilogue; stops at ret 0x82c74 *)
all: clear HS1; rename ms into ms1; fsw_aj_runU fsr_tbl_ok HS2 HJ3 HARU3.
all: lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ _ _ _ =>
      eapply (fsrD_awr B IMG);
      first
        [ solve [exact Usp]
        | solve [rewrite FR; lia]
        | solve [exact (fsr_pstat_FPc p k)]
        | solve [lazymatch goal with |- skeleton _ = skeleton _ => vm_compute; reflexivity end] ]
  | |- _ => idtac
  end.
all: assert (KB2 : forall x, b <= x < b + (n + HEAD) ->
  mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms)) x = mbyte tfibsegs (mrestrict (w_H W2) memT) x)
  by (intros x Hx; destruct (BLK x Hx) as (Hx64 & Hxs & Hxi); rewrite <- (KB1 x Hx);
      apply (fsrD_mbyte_frame E _ _ _ x HFr Hx64);
      apply fsrD_nwr; [lazymatch goal with |- skeleton _ = _ => vm_compute; reflexivity end | rewrite Usp; exact Hxs
      | exact Hxi]).
all: clear HF HFr HG KB1.
(* the registers at the ret *)
all: pose proof (fsw_reg_extra (w_H W2) regs3 (fs_extraT ++ xs) _ ms 1%bv 12 HS2 ltac:(vm_compute; reflexivity))
  as R1.
all: change (nth 12 (fs_extraT ++ xs) (Z_to_bv 64 0)) with (YK11.getr regs 1) in R1.
all: assert (Hjr : v_jalr (YK11.getr (ms_regs ms) 1) 0 = YK11.getr regs 1) by (rewrite R1; exact Hra0).
all: assert (R10 : YK11.getr (ms_regs ms) 10 = w64 (b + HEAD))
  by (apply bv_eq; rewrite (fsw_reg_off (w_H W2) E _ ms 10%bv 18 16 b HS2 ltac:(vm_compute; reflexivity) E18
        ltac:(unfold HEAD in *; lia));
      unfold w64, HEAD; rewrite unsigned_lit_small by (unfold HEAD in *; lia); reflexivity).
all: assert (HPf : aregs_preserved regs (ms_regs ms))
  by (intros r Hr;
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (clear - Hr; unfold acallee_saved in Hr; lia);
    clear Hr; repeat (destruct Hc as [-> | Hc]); try subst r;
    rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E _ ms _ HS2);
    lazymatch goal with |- sv_denot _ (sr_get (ss_regs ?s) ?q) = _ =>
      let v := eval vm_compute in (sr_get (ss_regs s) q) in change (sr_get (ss_regs s) q) with v end;
    first
      [ solve [exact (fsw_sp_back regs3 (fs_extraT ++ xs) regs 64 Usp)]
      | solve [rewrite fsw_SOff0; reflexivity]
      | solve [apply (fsrD_kept_reg regs regs3 regsT (fs_extraT ++ xs));
               [ vm_compute; reflexivity
               | unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
                   let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia
               | exact HP3
               | first [ etransitivity; [exact HKgp | symmetry; exact Hgp0]
                       | etransitivity; [exact HKtp | symmetry; exact Htp0]
                       | apply HK1; lia ] ]] ]).
(* the return, arm (c) of the post at res = b + HEAD *)
all: unfold fsr_post_c; apply (fsrD_ex _ _ _ (b + HEAD)); cbv beta.
all: pose proof (st_ok_mem_ok tfibsegs E _ _ HS2) as HM; cbn [restrict ms_mem] in HM.
all: eapply (fsw_retU B fsr_tbl fsr_tbl_ok W2 E _ ms _ STK_fuzz_realloc (spZ regs) (fsr_FPc p k) regs ly S U W mem md
  ly2 S2 _ 3 _ HS2 eq_refl ltac:(vm_compute; reflexivity) Hjr HJ3 HARU3 HPf).
all: intros mat2; cbv beta.
all: replace (b + HEAD - HEAD) with b by lia.
all: split; [exact R10|].
all: split; [unfold HEAD; lia|].
all: split; [exists b1, b2, (b1 ++ b2), []; split; [exact Eab|]; split; [exact Eab2 | apply app_nil_r]|].
all: split; [exact FH2|].
all: split;
  [ intros _; unfold fs_rblock; replace (b + HEAD - HEAD) with b by lia;
    split; [exact Hin|]; split; [unfold HEAD; replace (b + 16) with (b + 1 * 16) by lia; rewrite Z.mod_add by lia;
    exact Hb16|]; split; [lia|];
    apply (fsrD_val_mem_keep (mrestrict (w_H W2) memT) _ b 8 n); [intros x Hx; apply KB2; unfold HEAD; lia | exact HV]
  |].
all: split;
  [ unfold zbytes_at in HZ |- *;
    apply (fsrD_garr8_keep (mrestrict (w_H W2) memT) _ (b + HEAD) _); [|exact HZ];
    intros x Hx; apply KB2; pose proof (firstn_le_length (Z.to_nat (Z.min k n)) old); unfold HEAD in *; lia
  |].
all: lazymatch type of HS2 with st_ok _ _ ?s _ =>
  let fl := eval vm_compute in (fs_pstat_find (ss_mem s) G_LIVE) in
  let fp := eval vm_compute in (fs_pstat_find (ss_mem s) G_PEAK) in
  lazymatch fl with Some ?el => lazymatch fp with Some ?ep =>
    apply (fs_glob_of_TS E W2 (ms_mem ms) (ss_mem s) _ _ _ _ el ep (SOff 33 0) (SOff 34 0) HM)
  end end end.
all: first
  [ solve [lazymatch goal with |- fs_pstat_find _ _ = _ => vm_compute; reflexivity end]
  | solve [rewrite denot_lit_U, Usum; reflexivity]
  | solve [rewrite Z.max_l by lia; rewrite denot_lit_U, U36; reflexivity]
  | solve [rewrite Z.max_r by lia; rewrite denot_lit_U, Usum; reflexivity]
  | solve [rewrite fsw_SOff0; reflexivity]
  | solve [lia] ].
Qed.
End d.
