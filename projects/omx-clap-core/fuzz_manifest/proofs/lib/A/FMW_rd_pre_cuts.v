(* lv2_locate_manifest_readings, entry segment PRE: the segment's internal cuts and what the pieces share.
   PRE runs 0x81c04 .. {RD_R, RD_L} (readings_names.dis lines 10-78); its pieces (one file each):
     FMW_rd_pre.v     0x81c04 .. strlen .. fuzz_malloc .. RD_C2 (and the exits uri_len = 0, NULL), rd_E_holds
     FMW_rd_pre_c2.v  RD_C2 0x81c70 (fuzz_malloc returned whole) .. snprintf .. RD_C3   rdp_seg_C2
     FMW_rd_pre_c3.v  RD_C3 0x81c90 (after snprintf) .. strstr .. RD_C4                rdp_seg_C3
     FMW_rd_pre_c4.v  RD_C4 0x81c9c (after strstr) .. fuzz_free .. RD_C5               rdp_seg_C4
     FMW_rd_pre_c5.v  RD_C5 0x81ca8 (after fuzz_free) .. RD_R (found) / the stores .. RD_L   rdp_seg_C5
   Inside the poison window (C2 .. C4) the journal is over `unpoison [(whole - 16, 16)] mem` (FMupoison.v), the
   other facts over the real memory. Every cut carries: readings' journal from its entry (rd_com's form), the
   registers (rdp_regs + the live ones), the prologue's frame (rdp_pro, rdp_ke), the block and statics facts. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit FMW_rd_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_cuts FMW_rd_ret ACej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_rd_pre_k.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a value chunk of a region, looked up by offset *)
Fixpoint rdp_chunk_at (cs : list YP09.chunk) (o : Z) : option sv :=
  match cs with
  | [] => None
  | c :: t => match YP09.c_val c with
              | CVal w e => if (YP09.c_off c =? o) && (w =? 8)%N then Some e else rdp_chunk_at t o
              | _ => rdp_chunk_at t o
              end
  end.
Lemma rdp_chunk_at_In : forall cs o e, rdp_chunk_at cs o = Some e -> In (YP09.mkChunk o (CVal 8 e)) cs.
Proof.
induction cs as [|[co cv] t IH]; intros o e H; cbn in H; [discriminate|].
destruct cv as [w e' | ? | ? | ? ? ?]; try (right; apply IH; exact H).
destruct ((co =? o) && (w =? 8)%N) eqn:E; [|right; apply IH; exact H].
apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply N.eqb_eq in E2. injection H as <-. subst. left. reflexivity.
Qed.

Ltac rdp_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
(* the goal's configuration as cfg_at pc *)
Ltac rdp_cfg pc := lazymatch goal with |- SRr ?s ?W (mkCfg (mkst ?r (Z_to_bv 64 ?p) ?m ?rom) ?md) ?Q =>
  change (SRr s W (mkCfg (mkst r (Z_to_bv 64 p) m rom) md) Q) with (SRr s W (cfg_at tfibsegs pc r m md) Q) end.
(* a run's write windows: stack regions based at atom 2 = sp0 + d, the rest read only *)
Ltac rdp_awr dd E2 := lazymatch goal with |- awr_ok _ _ ?E ?rs _ _ _ _ _ _ _ =>
  let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
    | eapply awr_ok_cons_stack_off with (n := 2%nat) (d := dd);
      [reflexivity | exact E2 | cbn [YP09.r_wlo YP09.r_whi]; change STK_readings with 16624; lia
      | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
(* registers a run left as their own atoms *)
Ltac rdp_keep HS regs0 r Q :=
  pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs0 [] [r] HS (env_agree_refl _ _) ltac:(vm_compute; reflexivity) r
    ltac:(left; reflexivity)) as Q; cbn [ms_regs restrict] in Q.
(* the state after a run: name its machine state *)
Ltac rdp_name HS m := lazymatch type of HS with st_ok _ _ _ (restrict _ ?x) => rename x into m end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable CTX : list (list Z).
Hypothesis IMG : fm_img_facts tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Abbreviation rdJ cx := (ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx)
  (cx_W cx) (cx_mem cx) (cx_md cx) []).

(* ---- what PRE carries from the prologue to its exits ---- *)
(* the prologue's memory m1: the saved registers, readings' out-parameter slot and names' saved ra as at the entry *)
Definition rdp_pro (cx : rdcx) (m1 : word -> option byte) : Prop :=
  rd_saved_ok cx (cx_W cx) m1 /\
  (forall a, cx_sp cx <= a < cx_sp cx + 16 -> aview tfibsegs (w_H (cx_W cx)) m1 a = aview tfibsegs (w_H (cx_W cx)) (cx_mem cx) a).
(* [sp - 104, sp + 16) kept since the prologue *)
Definition rdp_ke (cx : rdcx) (m1 : word -> option byte) (W3 : world tfibsegs) (mem3 : word -> option byte) : Prop :=
  forall a, cx_sp cx - 104 <= a < cx_sp cx + 16 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H (cx_W cx)) m1 a.
(* sp = F, gp, tp, s0 = the shadow base, s1 = rp, s2 = uri, s8 = text *)
Definition rdp_regs (cx : rdcx) (regs3 : bvmap 5 word) : Prop :=
  getr regs3 2 = w64 (cx_F cx) /\ getr regs3 3 = getr (cx_regs cx) 3 /\ getr regs3 4 = getr (cx_regs cx) 4 /\
  getr regs3 8 = w64 SHADOW_OFF /\ getr regs3 9 = w64 (cx_sp cx) /\ getr regs3 18 = w64 (cx_u cx) /\
  getr regs3 24 = w64 (cx_t cx).

Lemma rdp_regs_pres : forall cx regs regs', aregs_preserved regs regs' -> rdp_regs cx regs -> rdp_regs cx regs'.
Proof.
intros cx regs regs' HP (R2 & R3 & R4 & R8 & R9 & R18 & R24).
repeat split; (rewrite (rdp_pres regs regs'); [assumption | exact HP | rdp_cs]).
Qed.
Lemma rdp_regs_run : forall cx H regs0 ss ms, st_ok tfibsegs (Ereg regs0 []) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 8; 9; 18; 24]%bv = true ->
  rdp_regs cx regs0 -> rdp_regs cx (ms_regs ms).
Proof.
intros cx H regs0 ss ms HS Hc (R2 & R3 & R4 & R8 & R9 & R18 & R24).
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs0 [] _ HS (env_agree_refl _ _) Hc) as K. cbn [ms_regs restrict] in K.
repeat split; (rewrite K; [assumption | cbv [In]; repeat (first [left; reflexivity | right])]).
Qed.
Lemma rdp_regs4_run : forall cx H regs0 ss ms, st_ok tfibsegs (Ereg regs0 []) ss (restrict H ms) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 8]%bv = true ->
  rdp_regs cx regs0 ->
  getr (ms_regs ms) 2 = w64 (cx_F cx) /\ getr (ms_regs ms) 3 = getr (cx_regs cx) 3 /\
  getr (ms_regs ms) 4 = getr (cx_regs cx) 4 /\ getr (ms_regs ms) 8 = w64 SHADOW_OFF.
Proof.
intros cx H regs0 ss ms HS Hc (R2 & R3 & R4 & R8 & _).
pose proof (g3_regs_of_st_ok tfibsegs _ _ _ regs0 [] _ HS (env_agree_refl _ _) Hc) as K. cbn [ms_regs restrict] in K.
repeat split; (rewrite K; [assumption | cbv [In]; repeat (first [left; reflexivity | right])]).
Qed.

(* rd_com at an exit (U = []) *)
Lemma rdp_com_of : forall cx k ly3 S3 W3 regs3 mem3 md3 m1,
  rd_base B CTX cx -> rdJ cx ly3 S3 W3 mem3 md3 k -> 0 <= k <= EV_names ->
  getr regs3 2 = w64 (cx_F cx) -> getr regs3 3 = getr (cx_regs cx) 3 -> getr regs3 4 = getr (cx_regs cx) 4 ->
  getr regs3 8 = w64 SHADOW_OFF ->
  rdp_pro cx m1 -> rdp_ke cx m1 W3 mem3 ->
  (forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B ly3 S3)) ->
  rd_com B cx k [] ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx k ly3 S3 W3 regs3 mem3 md3 m1 HB HJ Hk R2 R3 R4 R8 (HSV & K16) KE Hinc.
destruct HB as (HAN & _ & HRO & _ & _ & _ & _ & _ & _ & _ & Ct & Cu & Kt & Ku & _).
assert (HRO3 : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W3) mem3))
  by (eapply rdp_arodata_kept; [exact HJ | exact HRO]).
unfold rd_com. split; [exact HJ|]. split; [exact Hk|].
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|].
split.
{ unfold rd_saved_ok in *. apply Forall_forall. intros s Hs. pose proof (proj1 (Forall_forall _ _) HSV s Hs) as V.
  assert (Ho : 104 <= fst s <= 200)
    by (cbv [RD_SAVED In] in Hs; repeat (destruct Hs as [<-|Hs]; [cbn; lia|]); destruct Hs).
  apply (g3_val_mem_kept (cx_W cx) W3 m1 mem3); [exact V|]. intros i Hi. cbn in Hi. apply KE. unfold cx_F. lia. }
split.
{ intros a Ha. rewrite (KE a ltac:(lia)). exact (K16 a ltac:(lia)). }
split; [exact HRO3|].
split; [eapply (rdp_cstr_kept B); [exact IMG | exact HJ | exact Hinc | exact g3_pstat_img | exact HRO3 | exact Kt | exact Ct]|].
split; [eapply (rdp_cstr_kept B); [exact IMG | exact HJ | exact Hinc | exact g3_pstat_img | exact HRO3 | exact Ku | exact Cu]|].
split; [exact (rdp_cstr_kept_kept B _ _ _ _ _ _ Hinc Kt) | exact (rdp_cstr_kept_kept B _ _ _ _ _ _ Hinc Ku)].
Qed.

(* *rp = v at an exit *)
Lemma rdp_rp : forall cx m1 W3 mem3, rd_base B CTX cx -> rdp_pro cx m1 -> rdp_ke cx m1 W3 mem3 ->
  val_mem tfibsegs (rdW W3 mem3) (cx_sp cx) 8 (cx_v cx).
Proof.
intros cx m1 W3 mem3 HB (_ & K16) KE. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & Hv & _).
apply (g3_val_mem_kept (cx_W cx) W3 (cx_mem cx) mem3); [exact Hv|]. intros i Hi. cbn in Hi.
rewrite (KE (cx_sp cx + i) ltac:(lia)). apply K16. lia.
Qed.

(* the statics are image bytes below the shadow *)
Lemma rdp_glob_low : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  fm_glob tfibsegs W m live peak cnt fail ->
  (forall a, 0 <= a < kLowMemEnd -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fm_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail (GL & GP & GC & GF & R) HK. pose proof asan_consts as (_ & _ & _ & _ & C5).
unfold fm_glob. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (g3_val_mem_kept W W' m m'); [exact GL | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' m m'); [exact GP | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' m m'); [exact GC | intros i Hi; apply HK; cbn in Hi; lia]|].
split; [apply (g3_val_mem_kept W W' m m'); [exact GF | intros i Hi; apply HK; cbn in Hi; lia]|].
exact R.
Qed.

(* a slot of region 0 after a run *)
Lemma rdp_slot : forall E ss (W : world tfibsegs) ms lo hi wlo whi cs o e v b,
  st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
  rdp_chunk_at cs o = Some e -> bv_unsigned (ew E 2) = b ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs (rdW W (ms_mem ms)) (b + o) 8 v.
Proof.
intros E ss W ms lo hi wlo whi cs o e v b HS Hn Hc Hb He Hv.
pose proof (g3_st_ok_region_nth E ss (restrict (w_H W) ms) 0 _ HS Hn) as HR. cbn [ms_mem restrict] in HR.
exact (g3_field_of_region E _ 2 b cs lo hi wlo whi o 8%N e v HR Hb (rdp_chunk_at_In cs o e Hc) He
  ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.

(* the shadow band lies below the high application memory *)
Lemma rdp_band : forall x, 0 <= x < alloc_ceiling -> SHADOW_OFF <= shadow_addr x /\ shadow_addr x + 16 <= kHighMemBeg.
Proof.
intros x Hx. pose proof asan_consts as (C1 & _ & C3 & _). unfold shadow_addr, SHADOW_OFF. rewrite C3.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44 - 16) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* a kept C string inside the window: from the journal (unpoisoned view) to the real memory *)
Lemma rdp_kept_win : forall cx lyc Sc Wc memc mdc k h n0 p l,
  rdJ cx lyc Sc Wc (unpoison [(h, 16)] memc) mdc k ->
  ablocks B lyc Sc = ablocks B (cx_ly cx) (cx_S cx) ++ [(h, n0)] -> 16 <= n0 ->
  0 <= h -> h mod 8 = 0 -> h + 16 <= kHighMemEnd ->
  upoisoned tfibsegs Wc memc [(h, 16)] ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W cx)) (cx_mem cx)) ->
  cstr_kept B (cx_ly cx) (cx_S cx) p l -> cstr_ok tfibsegs (cx_W cx) (cx_mem cx) p l ->
  cstr_ok tfibsegs Wc memc p l.
Proof.
intros cx lyc Sc Wc memc mdc k h n0 p l HJ Eab Hn0 H0 H8 H1 Hpo HRO Hk Hc.
pose proof HJ as (HARc & _).
assert (Hinc : forall x, In x (ablocks B (cx_ly cx) (cx_S cx)) -> In x (ablocks B lyc Sc))
  by (intros x Hx; rewrite Eab; apply in_or_app; left; exact Hx).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H Wc) (unpoison [(h, 16)] memc)))
  by (eapply rdp_arodata_kept; [exact HJ | exact HRO]).
apply (rdp_cstr_unp Wc memc h p l H0 H8 H1); [|exact Hpo|].
- intros x Hx Hx2. apply (rdp_kept_disj B _ _ _ _ _ _ _ p l h n0 HARc Eab ltac:(lia) Hk x Hx). lia.
- eapply (rdp_cstr_kept B); [exact IMG | exact HJ | exact Hinc | exact g3_pstat_img | exact HROc | exact Hk | exact Hc].
Qed.

(* the image facts a runtime call inside the window takes *)
Lemma rdp_img_win : forall cx lyc Sc Wc memc mdc k h,
  rdJ cx lyc Sc Wc (unpoison [(h, 16)] memc) mdc k -> 0 <= h -> h + 16 <= kHighMemEnd ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W cx)) (cx_mem cx)) ->
  rom_viewN tfibsegs B Wc memc /\ fm_canary tfibsegs Wc memc /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H Wc) memc) /\
  (forall f ps, In (f, ps) FM_SN_FMTS -> cstr_ok tfibsegs Wc (unpoison [(h, 16)] memc) f (fmt_bytes ps)).
Proof.
intros cx lyc Sc Wc memc mdc k h HJ H0 H1 HRO.
pose proof HJ as (HARc & _).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H Wc) (unpoison [(h, 16)] memc)))
  by (eapply rdp_arodata_kept; [exact HJ | exact HRO]).
destruct (IMG _ _ _ _ _ HARc HROc) as (Hrv & _ & Hcan & _ & Hfm).
split; [exact (rdp_rom_view_unp B Wc h memc H0 H1 Hrv)|].
split; [exact (rdp_canary_unp Wc h memc H0 H1 Hcan)|].
split; [exact (rdp_arodata_unp B Wc h memc H0 H1 HROc)|].
intros f ps Hf. exact (proj1 (Hfm f ps Hf)).
Qed.
(* the owned read-only bytes (the string contracts' rom_viewO) inside the window *)
Lemma rdp_img_winO : forall cx lyc Sc Wc memc mdc k h,
  rdJ cx lyc Sc Wc (unpoison [(h, 16)] memc) mdc k -> 0 <= h -> h + 16 <= kHighMemEnd ->
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H (cx_W cx)) (cx_mem cx)) ->
  rom_viewO tfibsegs B Wc memc.
Proof.
intros cx lyc Sc Wc memc mdc k h HJ H0 H1 HRO.
pose proof HJ as (HARc & _).
assert (HROc : arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H Wc) (unpoison [(h, 16)] memc)))
  by (eapply rdp_arodata_kept; [exact HJ | exact HRO]).
destruct (IMG _ _ _ _ _ HARc HROc) as (_ & Hro & _).
exact (rdp_rom_viewO_unp B Wc h memc H0 H1 Hro).
Qed.

(* the whole string "<uri>" just written into the fresh block (h, n0): a C string *)
Lemma rdp_whole_cstr : forall lyc Sc Wc memc mdc h n0 ub,
  AR tfibsegs B lyc Sc Wc (unpoison [(h, 16)] memc) mdc -> In (h, n0) (ablocks B lyc Sc) ->
  n0 = Z.of_nat (length ub) + 3 + 16 -> (length ub <= 255)%nat -> Forall (fun c => c <> 0) ub ->
  bytes_at tfibsegs Wc memc (h + 16) (rdp_out ub ++ [0]) ->
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF (h + 16) (n0 - 16) ->
  shadow_hull_vis (aview tfibsegs (w_H Wc) memc) (h + 16) (n0 - 16) ->
  cstr_ok tfibsegs Wc memc (h + 16) (rdp_out ub).
Proof.
intros lyc Sc Wc memc mdc h n0 ub HAR Hin En0 Hl Hnz Hby HRA Hhv.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (rdp_blk_slack B _ _ _ _ _ h n0 HAR Hin ltac:(lia)) as [Hhi Hsl].
pose proof (al_blocks _ _ (AR_laws_ok tfibsegs B) _ _ _ _ _ _ _ HAR Hin) as (_ & Hh4 & _).
assert (Lo : Z.of_nat (length (rdp_out ub)) = Z.of_nat (length ub) + 2) by (rewrite rdp_out_len; lia).
split; [split; [exact Hby|]|].
{ unfold rdp_out. constructor; [lia|]. apply Forall_app. split; [exact Hnz | constructor; [lia | constructor]]. }
rewrite Lo. split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold amem_range; right; lia|].
split; [replace (Z.of_nat (length ub) + 2 + 1) with (n0 - 16) by lia; exact HRA|].
split; [replace (Z.of_nat (length ub) + 2 + 1) with (n0 - 16) by lia; exact Hhv|].
intros a Ha.
rewrite <- (rdp_aview_unp (w_H Wc) h memc a ltac:(lia) ltac:(lia)); [| |right; lia].
- apply (rdp_block_tail_vis B lyc Sc Wc _ mdc h n0 HAR Hin ltac:(lia)).
  replace (h + n0 - 1) with (h + 16 + (Z.of_nat (length ub) + 2)) by lia.
  pose proof (Z.mod_pos_bound (h + 16 + (Z.of_nat (length ub) + 2)) 8 ltac:(lia)). lia.
- pose proof (Z.mod_pos_bound (h + 16 + (Z.of_nat (length ub) + 2)) 8 ltac:(lia)). lia.
Qed.

(* a byte range left of / right of a block it misses *)
Lemma rdp_rng_split : forall p L b m d n,
  (forall x, p <= x <= p + L -> ~ (b <= x < b + m)) -> b <= d -> d + n <= b + m -> 0 <= L -> 0 < n ->
  p + L + 1 <= d \/ d + n <= p.
Proof.
intros p L b m d n H Hd Hn HL Hn0.
destruct (Z_le_gt_dec (p + L + 1) d) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (d + n) p) as [H2|H2]; [right; exact H2|].
exfalso. apply (H (Z.max p d)); lia.
Qed.

(* ======== the cuts ======== *)
(* RD_C5 0x81ca8, after fuzz_free: the window closed (U = []), k = EV_names, s5 = strstr's answer v *)
Definition rdp_seg_C5 : Prop :=
  forall cx m1 ly5 S5 W5 regs5 mem5 md5 v,
  rd_base B CTX cx -> rdJ cx ly5 S5 W5 mem5 md5 EV_names ->
  rdp_regs cx regs5 -> getr regs5 22 = w64 (cx_ulen cx) -> getr regs5 21 = w64 v -> 0 <= v < 2 ^ 64 ->
  rdp_pro cx m1 -> rdp_ke cx m1 W5 mem5 ->
  Permutation (ablocks B ly5 S5) (ablocks B (cx_ly cx) (cx_S cx)) ->
  fm_glob tfibsegs W5 mem5 (cx_live cx) (Z.max (cx_peak cx) (cx_live cx + cx_ulen cx + 3)) (cx_cnt cx + 1) (cx_fail cx) ->
  cx_cnt cx <> cx_fail cx -> cx_ub cx <> [] ->
  ((v = 0 /\ no_occ (cx_tb cx) (rdp_out (cx_ub cx))) \/
   (exists j, first_occ (cx_tb cx) (rdp_out (cx_ub cx)) j /\ v = cx_t cx + Z.of_nat j)) ->
  SRr tfibsegs W5 (mkCfg (mkst regs5 (Z_to_bv 64 RD_C5) mem5 (seg_rom tfibsegs)) md5) (rd_post B cx).

(* RD_C4 0x81c9c, after strstr: a0 = v (strstr's answer), s4 = whole = res; the head of the block (res - 16, n + 16)
   (n = uri_len + 3) user-poisoned *)
Definition rdp_seg_C4 : Prop :=
  forall cx m1 lyM SM WM regs4 mem4 md4 res v,
  rd_base B CTX cx -> rdJ cx lyM SM WM (unpoison [(res - 16, 16)] mem4) md4 1 ->
  rdp_regs cx regs4 -> getr regs4 22 = w64 (cx_ulen cx) -> getr regs4 20 = w64 res ->
  getr regs4 10 = w64 v -> 0 <= v < 2 ^ 64 ->
  rdp_pro cx m1 -> rdp_ke cx m1 WM mem4 ->
  upoison_ok B lyM SM [(res - 16, 16)] -> upoisoned tfibsegs WM mem4 [(res - 16, 16)] ->
  4096 + 16 <= res ->
  ablocks B lyM SM = ablocks B (cx_ly cx) (cx_S cx) ++ [(res - 16, cx_ulen cx + 3 + 16)] ->
  fm_rblock tfibsegs B lyM SM WM mem4 res (cx_ulen cx + 3) ->
  fm_glob tfibsegs WM mem4 (cx_live cx + (cx_ulen cx + 3)) (Z.max (cx_peak cx) (cx_live cx + (cx_ulen cx + 3)))
    (cx_cnt cx + 1) (cx_fail cx) ->
  cx_cnt cx <> cx_fail cx -> cx_ub cx <> [] ->
  ((v = 0 /\ no_occ (cx_tb cx) (rdp_out (cx_ub cx))) \/
   (exists j, first_occ (cx_tb cx) (rdp_out (cx_ub cx)) j /\ v = cx_t cx + Z.of_nat j)) ->
  SRr tfibsegs WM (mkCfg (mkst regs4 (Z_to_bv 64 RD_C4) mem4 (seg_rom tfibsegs)) md4) (rd_post B cx).

(* RD_C3 0x81c90, after snprintf: whole = "<uri>" NUL (bytes_at), s4 = whole = res *)
Definition rdp_seg_C3 : Prop :=
  forall cx m1 lyM SM WM regs3 mem3 md3 res,
  rd_base B CTX cx -> rdJ cx lyM SM WM (unpoison [(res - 16, 16)] mem3) md3 1 ->
  rdp_regs cx regs3 -> getr regs3 22 = w64 (cx_ulen cx) -> getr regs3 20 = w64 res ->
  rdp_pro cx m1 -> rdp_ke cx m1 WM mem3 ->
  upoison_ok B lyM SM [(res - 16, 16)] -> upoisoned tfibsegs WM mem3 [(res - 16, 16)] ->
  4096 + 16 <= res ->
  ablocks B lyM SM = ablocks B (cx_ly cx) (cx_S cx) ++ [(res - 16, cx_ulen cx + 3 + 16)] ->
  fm_rblock tfibsegs B lyM SM WM mem3 res (cx_ulen cx + 3) ->
  bytes_at tfibsegs WM mem3 res (rdp_out (cx_ub cx) ++ [0]) ->
  range_addressable (aview tfibsegs (w_H WM) mem3) SHADOW_OFF res (cx_ulen cx + 3) ->
  shadow_hull_vis (aview tfibsegs (w_H WM) mem3) res (cx_ulen cx + 3) ->
  fm_glob tfibsegs WM mem3 (cx_live cx + (cx_ulen cx + 3)) (Z.max (cx_peak cx) (cx_live cx + (cx_ulen cx + 3)))
    (cx_cnt cx + 1) (cx_fail cx) ->
  cx_cnt cx <> cx_fail cx -> cx_ub cx <> [] ->
  SRr tfibsegs WM (mkCfg (mkst regs3 (Z_to_bv 64 RD_C3) mem3 (seg_rom tfibsegs)) md3) (rd_post B cx).

(* RD_C2 0x81c70, fuzz_malloc returned whole = res (a0), s5 = n = uri_len + 3, s6 = uri_len (fuzz_malloc_spec's post) *)
Definition rdp_seg_C2 : Prop :=
  forall cx m1 lyM SM WM regsM memM mdM res,
  rd_base B CTX cx -> rdJ cx lyM SM WM (unpoison [(res - 16, 16)] memM) mdM 1 ->
  rdp_regs cx regsM -> getr regsM 22 = w64 (cx_ulen cx) -> getr regsM 21 = w64 (cx_ulen cx + 3) ->
  getr regsM 10 = w64 res ->
  rdp_pro cx m1 -> rdp_ke cx m1 WM memM ->
  upoison_ok B lyM SM [(res - 16, 16)] -> upoisoned tfibsegs WM memM [(res - 16, 16)] ->
  4096 + 16 <= res ->
  ablocks B lyM SM = ablocks B (cx_ly cx) (cx_S cx) ++ [(res - 16, cx_ulen cx + 3 + 16)] ->
  fm_rblock tfibsegs B lyM SM WM memM res (cx_ulen cx + 3) ->
  range_addressable (aview tfibsegs (w_H WM) memM) SHADOW_OFF res (cx_ulen cx + 3) ->
  shadow_hull_vis (aview tfibsegs (w_H WM) memM) res (cx_ulen cx + 3) ->
  fm_glob tfibsegs WM memM (cx_live cx + (cx_ulen cx + 3)) (Z.max (cx_peak cx) (cx_live cx + (cx_ulen cx + 3)))
    (cx_cnt cx + 1) (cx_fail cx) ->
  cx_cnt cx <> cx_fail cx -> cx_ub cx <> [] ->
  SRr tfibsegs WM (mkCfg (mkst regsM (Z_to_bv 64 RD_C2) memM (seg_rom tfibsegs)) mdM) (rd_post B cx).
End c.
