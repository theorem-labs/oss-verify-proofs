From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Model.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW8Kit RPgW8BlkA RPgW8BlkB RPgW8Rok RPgW8BlkC1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Definition w_exit (last : bool) : Z := if last then W_CLOSE else W_LOOP.

Lemma w_br_end_ok : forall E kk cnt last, bv_unsigned (ew E A_KK) = kk -> bv_unsigned (ew E A_CNT) = cnt ->
  0 <= kk <= 31 -> 1 <= cnt <= 32 -> (kk + 1 =? cnt) = last -> acond_ok E (br_end last).
Proof.
intros E kk cnt last U39 U40 Hkk Hcnt Hl. unfold acond_ok, br_end.
destruct last; cbn [ac_c ac_a ac_b]; [rewrite branch_eq_U | rewrite branch_ne_U];
rewrite (wU_off E A_KK 1 kk U39), (wU_off0 E A_CNT cnt U40) by lia; [| apply negb_true_iff]; exact Hl.
Qed.

(* ============================== run C, first = 0: 0x817f0 to the pod loop's exit ============================== *)
Lemma w_blkC0 : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (R F pp L sz kk cnt sF : Z) (last : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
(forall a, sF + 30 <= a < sF + 43 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
getr regs 9 = w64 R -> getr regs 19 = w64 sF -> getr regs 20 = w64 (shadow_addr (pp + 0x4000)) ->
getr regs 21 = w64 (pp + 0x4000) -> getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 pp ->
getr regs 24 = w64 (Model.pad8 sz) ->
Forall (fun c => val_mem rsegs (mrestrict (w_H W) mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp 0 kk cnt) ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4000) 8 (L + 8 + sz) ->
(forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) ->
(forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) ->
(forall o, 30 <= o < 43 -> apresent (w_H W) mem (sF + o)) ->
pp mod 16 = 0 -> in_app pp 19744 -> pp + 19744 <= alloc_ceiling ->
alloc_ceiling <= R -> R + 0x1a0 <= 2 ^ 47 -> 0 <= F < 2 ^ 47 ->
0x7fff8000 <= sF -> sF + 64 <= 0x10007fff8000 -> sF + 64 <= shadow_addr pp \/ shadow_addr pp + 2468 <= sF ->
0 <= L <= 5384 -> L mod 8 = 0 -> 0 <= sz <= 45 -> 0 <= kk <= 31 -> 1 <= cnt <= 32 -> (kk + 1 =? cnt) = last ->
SRr rsegs W (cfg_at rsegs W_C regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (w_exit last)) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 11 = w64 (kk + 1) /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4000) 8 (L + 8 + sz + Model.pad8 sz) /\
 (forall o, 30 <= o < 43 -> mbyte rsegs (mrestrict (w_H W) mem') (sF + o) = Some (Z_to_bv 8 248)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) -> ~ (sF + 30 <= a < sF + 43) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k R F pp L sz kk cnt sF last
HJ Hin Hfr HawF H9 H19 H20 H21 H23 H27 H24 HSL HLEN HSH HWR HWF Hpp16 Happ Hpphi HR1 HR2 HF HsF1 HsF2 HsFpp
HL HL8 Hsz Hkk Hcnt Hlast.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
destruct (wpp_zone pp Hpp16 Happ Hpphi) as (Hpplo & HshB & HshB2 & Hz).
pose proof (Model.pad8_bound sz) as Hpad.
set (E := Ereg regs (wext F L 0 0 0 sz 0 kk cnt 0)).
assert (HAE : env_agree 32 (Ereg regs (wext F L 0 0 0 sz 0 kk cnt 0)) E) by apply env_agree_refl.
destruct (wext_ew regs F L 0 0 0 sz 0 kk cnt 0) as (X32 & X33 & _ & _ & _ & X37 & X38 & X39 & X40 & X41).
fold E in X32, X33, X37, X38, X39, X40, X41.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (Hsh4 : shadow_addr (pp + 0x4000) = shadow_addr pp + 2048) by (rewrite wshadow_pp_L by (try lia; reflexivity); reflexivity).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), H19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr pp + 2048) by (rewrite (EE 20%nat 20%bv eq_refl), H20, Hsh4; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite (EE 23%nat 23%bv eq_refl), H23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = Model.pad8 sz) by (rewrite (EE 24%nat 24%bv eq_refl), H24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E A_SZ) = sz) by (rewrite X37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E A_FS) = 0) by (rewrite X38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E A_KK) = kk) by (rewrite X39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E A_CNT) = cnt) by (rewrite X40; apply unsigned_lit_small; lia).
assert (U41 : bv_unsigned (ew E A_NE) = 0) by (rewrite X41; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E (ssC0 last) (restrict (w_H W) (mkst regs (Z_to_bv 64 W_C) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC0. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | | | apply Forall_nil].
    + apply (rok_slots E _ mem R F pp 0 kk cnt U9 U27 U32 U38 U39 U40 HSL); lia.
    + apply (rok_len E _ mem pp _ (L + 8 + sz) U21); [ | exact HLEN | lia | | lia | lia].
      * unfold len_C. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (wU_off E A_L 8 L U33), (wU_off0 E A_SZ sz U37) by lia.
        apply zcanon_id. unfold M64. lia.
      * intros i Hi. replace (pp + 0x4000 + i) with (pp + (0x4000 + i)) by lia. apply HWR. lia.
    + apply (rok_sh4 E _ mem pp U20 HSH); lia.
    + apply (rok_fsh E _ mem sF U19 HWF); lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_slots r_lenv r_sh4 r_fsh].
    rewrite U9, U21, U20, U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hz as [Hz|Hz]; destruct HsFpp as [HsFpp|HsFpp]; repeat split; lia.
  - split; [|split].
    + cbn [f_atoms fC atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U27, U33, U37, U24, U38, U39, U40, U41.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
    + cbn [f_conds conds_ok]. split; [|split; [|exact I]].
      * unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, (wU_off0 E A_FS 0 U38), U_SLit by lia. reflexivity.
      * apply (w_br_end_ok E kk cnt last U39 U40 Hkk Hcnt Hlast).
    + cbn [f_alias alias_ok]. split; [| exact I]. apply (w_al_ne_ok E pp U27 U23 U20 Hpp8); lia. }
assert (Haw : forall a, pp <= a < pp + Layout.PP_SIZE ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
{ intros a Ha. replace a with (pp + (a - pp)) by lia. apply (rl_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hin | exact Hfr |].
  unfold req_size, Layout.PP_SIZE in *. cbn. lia. }
assert (Q24 : bv_unsigned (ew E 24) = Model.pad8 sz) by exact U24.
assert (Q33 : bv_unsigned (ew E 33) = L) by exact U33.
assert (Q37 : bv_unsigned (ew E 37) = sz) by exact U37.
assert (Q39 : bv_unsigned (ew E 39) = kk) by exact U39.
unfold cfg_at. change (w64 W_C) with (Z_to_bv 64 W_C).
destruct last; aj_run wtbl_ok HS HJ.
all: try (
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 ow) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact U21 | intros a Ha; apply Haw; unfold Layout.PP_SIZE; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |]
  | eapply awr_ok_cons_gen; [reflexivity | exact U19 | intros a Ha; apply HawF; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |] ]).
all: lazymatch goal with
  | HS1 : st_ok _ _ ?ssf (restrict _ ?msf), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _,
    HFr1 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; split; [reflexivity|];
    exists (ms_regs msf), (ms_mem msf), mdf;
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS1 eq_refl) at 1;
    rename HS1 into HSf, HJ1 into HJf, HFr1 into HFrf
  end.
all: lazymatch type of HSf with st_ok _ _ ?ssf ?msf =>
    let rl := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    let rf := eval vm_compute in (nth 3 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inl : In rl (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]));
    assert (Inf : In rf (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
all: pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inl Hc) as CL;
  cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in CL; rewrite U21 in CL.
all: split; [reflexivity|].
all: split; [exact HJf|].
all: split; [apply RPgCfgChanges.same_io_wvb|].
all: split; [wreg HSf (11%bv : bv 5); cbn [sv_denot]; rewrite Q39; reflexivity|].
all: split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
all: split; [
  pose proof (CL _ ltac:(cbn; left; reflexivity)) as C0; apply w_chunk8 in C0; rewrite Z.add_0_r in C0;
  replace (L + 8 + sz + Model.pad8 sz) with (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 24 8) (SOff 33 0)) (SOff 37 0))); [exact C0|];
  rewrite !U_SAlu; cbn [zalu_raw]; rewrite (wU_off E 24 8 _ Q24), (wU_off0 E 33 L Q33), (wU_off0 E 37 sz Q37) by lia;
  rewrite (zcanon_id (Model.pad8 sz + 8 + L)) by (unfold M64; lia); rewrite zcanon_id by (unfold M64; lia); lia|].
all: split; [exact (w_fsh_out E _ _ sF HSf U19 Inf)|].
all: intros a Ha H1 H2; apply aview_eq_of; apply HFrf; rewrite unsigned_lit_small by exact Ha;
  intros (r & Hr & Hw); unfold ssC0 in Hr; cbn [ss_mem In] in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_slots r_lenv r_sh4 r_fsh] in Hw; try lia.
Qed.

(* ============================== run D: after the record's memcpy, 0x81850 to the pod loop's exit ============================== *)
Lemma w_blkD : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (R F pp kk cnt sF : Z) (last : bool),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
(forall a, sF + 30 <= a < sF + 43 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a) ->
getr regs 9 = w64 R -> getr regs 19 = w64 sF -> getr regs 27 = w64 pp ->
Forall (fun c => val_mem rsegs (mrestrict (w_H W) mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp 1 kk cnt) ->
(forall o, 30 <= o < 43 -> apresent (w_H W) mem (sF + o)) ->
alloc_ceiling <= R -> R + 0x1a0 <= 2 ^ 47 -> 0 <= F < 2 ^ 47 -> 4096 <= pp < 2 ^ 47 ->
0x7fff8000 <= sF -> sF + 64 <= 0x10007fff8000 ->
0 <= kk <= 31 -> 1 <= cnt <= 32 -> (kk + 1 =? cnt) = last ->
SRr rsegs W (cfg_at rsegs W_D regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (w_exit last)) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 11 = w64 (kk + 1) /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 (forall o, 30 <= o < 43 -> mbyte rsegs (mrestrict (w_H W) mem') (sF + o) = Some (Z_to_bv 8 248)) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sF + 30 <= a < sF + 43) -> aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k R F pp kk cnt sF last
HJ HawF H9 H19 H27 HSL HWF HR1 HR2 HF Hpp HsF1 HsF2 Hkk Hcnt Hlast.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
set (E := Ereg regs (wext F 0 0 0 0 0 1 kk cnt 0)).
assert (HAE : env_agree 32 (Ereg regs (wext F 0 0 0 0 0 1 kk cnt 0)) E) by apply env_agree_refl.
destruct (wext_ew regs F 0 0 0 0 0 1 kk cnt 0) as (X32 & _ & _ & _ & _ & _ & X38 & X39 & X40 & _).
fold E in X32, X38, X39, X40.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = sF) by (rewrite (EE 19%nat 19%bv eq_refl), H19; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E A_FS) = 1) by (rewrite X38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E A_KK) = kk) by (rewrite X39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E A_CNT) = cnt) by (rewrite X40; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E (ssD last) (restrict (w_H W) (mkst regs (Z_to_bv 64 W_D) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssD. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | apply Forall_nil].
    + apply (rok_slots E _ mem R F pp 1 kk cnt U9 U27 U32 U38 U39 U40 HSL); lia.
    + apply (rok_fsh E _ mem sF U19 HWF); lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_slots r_fsh].
    rewrite U9, U19. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U39, U40. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
    + cbn [f_conds conds_ok]. split; [apply (w_br_end_ok E kk cnt last U39 U40 Hkk Hcnt Hlast) | exact I].
    + exact I. }
assert (Q39 : bv_unsigned (ew E 39) = kk) by exact U39.
unfold cfg_at. change (w64 W_D) with (Z_to_bv 64 W_D).
destruct last; aj_run wtbl_ok HS HJ.
all: try (
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 ow) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | exact U19 | intros a Ha; apply HawF; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |] ]).
all: lazymatch goal with
  | HS1 : st_ok _ _ ?ssf (restrict _ ?msf), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _,
    HFr1 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; split; [reflexivity|];
    exists (ms_regs msf), (ms_mem msf), mdf;
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS1 eq_refl) at 1;
    rename HS1 into HSf, HJ1 into HJf, HFr1 into HFrf
  end.
all: lazymatch type of HSf with st_ok _ _ ?ssf ?msf =>
    let rf := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inf : In rf (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
all: split; [reflexivity|].
all: split; [exact HJf|].
all: split; [apply RPgCfgChanges.same_io_wvb|].
all: split; [wreg HSf (11%bv : bv 5); cbn [sv_denot]; rewrite Q39; reflexivity|].
all: split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
all: split; [exact (w_fsh_out E _ _ sF HSf U19 Inf)|].
all: intros a Ha H1; apply aview_eq_of; apply HFrf; rewrite unsigned_lit_small by exact Ha;
  intros (r & Hr & Hw); unfold ssD in Hr; cbn [ss_mem In] in Hr;
  destruct Hr as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_slots r_fsh] in Hw; try lia.
Qed.
End w.
