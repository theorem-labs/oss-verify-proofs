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
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgW8Kit RPgW8BlkA RPgW8BlkB RPgW8Rok.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws rsegs B := YG0q.AR_laws_ok rsegs B.

Lemma w_chunk4v : forall E m base off v, YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 4 v)) ->
val_mem rsegs m (base + off) 4 (U E v).
Proof.
intros E m base off v H kk Hk. destruct (H (Z.of_nat kk) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [cbyte YP09.c_val YP09.c_off] in Hb, Hm. rewrite Hm. injection Hb as <-. f_equal.
unfold byte_of_word. rewrite rm_le_byte_bv by exact Hk. reflexivity.
Qed.

(* the alias of n_ent's shadow cell, as run A states it *)
Lemma w_al_ne_ok : forall E pp, bv_unsigned (ew E 27) = pp -> bv_unsigned (ew E 23) = SHADOW_OFF ->
  bv_unsigned (ew E 20) = shadow_addr pp + 2048 -> pp mod 8 = 0 -> 4096 <= pp -> pp + 19744 <= 2 ^ 47 ->
  sv_denot E (fst al_ne) = sv_denot E (snd al_ne).
Proof.
intros E pp U27 U23 U20 Hpp8 Hlo Hhi. unfold al_ne. cbn [fst snd].
assert (Hppd : (pp + 0x4d14) / 8 = pp / 8 + 2466).
{ rewrite (Z.div_mod pp 8) at 1 by lia. rewrite Hpp8.
  replace (8 * (pp / 8) + 0 + 0x4d14) with (4 + (pp / 8 + 2466) * 8) by lia.
  rewrite Z.div_add by lia. reflexivity. }
assert (Hshp : shadow_addr pp = SHADOW_OFF + pp / 8) by reflexivity.
pose proof (Z.div_pos pp 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le pp 8 ltac:(lia)).
unfold SHADOW_OFF in *.
apply U_inj. rewrite !U_SAlu, !U_SOff, !U_SLit, U27, U23, U20. cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3.
rewrite (zcanon_id (pp + 0x4d14)) by (unfold M64; lia). rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Hppd. rewrite (zcanon_id (pp / 8 + 2466)) by (unfold M64; lia).
rewrite Hshp. rewrite (zcanon_id (0x7fff8000 + 0)) by (unfold M64; lia).
rewrite !zcanon_id by (unfold M64; lia). lia.
Qed.

(* ============================== run C, first = 1: 0x817f0 to the record's memcpy ============================== *)
Lemma w_blkC1 : forall STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k (R F pp L sz kk cnt ne : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem md k ->
In (pp, Layout.PP_SIZE) (ablocks B ly2 S2) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
getr regs 9 = w64 R -> getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 pp -> getr regs 24 = w64 (Model.pad8 sz) ->
Forall (fun c => val_mem rsegs (mrestrict (w_H W) mem) (R + fst c) 8 (snd c mod 2 ^ 64)) (wslot_vals F pp 1 kk cnt) ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4000) 8 (L + 8 + sz) ->
val_mem rsegs (mrestrict (w_H W) mem) (pp + 0x4d14) 4 ne ->
(forall i, 0 <= i < 2468 -> aview rsegs (w_H W) mem (shadow_addr pp + i) = Some 0) ->
(forall i, 0 <= i < 19744 -> apresent (w_H W) mem (pp + i)) ->
pp mod 16 = 0 -> in_app pp 19744 -> pp + 19744 <= alloc_ceiling ->
alloc_ceiling <= R -> R + 0x1a0 <= 2 ^ 47 -> 0 <= F < 2 ^ 47 ->
0 <= L <= 5384 -> L mod 8 = 0 -> 0 <= sz <= 45 -> 0 <= kk <= 31 -> 1 <= cnt <= 32 -> 0 <= ne <= 31 ->
SRr rsegs W (cfg_at rsegs W_C regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 W_MEMCPY) mem' (seg_rom rsegs)) md' /\
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W mem' md' k /\ same_io md md' /\
 getr regs' 1 = w64 0x81850 /\ getr regs' 10 = w64 (pp + 0x4014 + 104 * ne) /\ getr regs' 11 = w64 (F + 0xf0) /\
 getr regs' 12 = w64 104 /\
 (forall r, In r wkeep -> getr regs' r = getr regs r) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4000) 8 (L + 8 + sz + Model.pad8 sz) /\
 val_mem rsegs (mrestrict (w_H W) mem') (pp + 0x4d14) 4 (ne + 1) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (pp + 0x4000 <= a < pp + 0x4000 + 8) -> ~ (pp + 0x4d14 <= a < pp + 0x4d14 + 4) ->
  aview rsegs (w_H W) mem' a = aview rsegs (w_H W) mem a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W regs mem md k R F pp L sz kk cnt ne
HJ Hin Hfr H9 H20 H21 H23 H27 H24 HSL HLEN HNE HSH HWR Hpp16 Happ Hpphi HR1 HR2 HF HL HL8 Hsz Hkk Hcnt Hne.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof YM05.alloc_ceiling_val as Hceil.
destruct (wpp_zone pp Hpp16 Happ Hpphi) as (Hpplo & HshB & HshB2 & Hz).
pose proof (Model.pad8_bound sz) as Hpad.
set (E := Ereg regs (wext F L 0 0 0 sz 1 kk cnt ne)).
assert (HAE : env_agree 32 (Ereg regs (wext F L 0 0 0 sz 1 kk cnt ne)) E) by apply env_agree_refl.
destruct (wext_ew regs F L 0 0 0 sz 1 kk cnt ne) as (X32 & X33 & _ & _ & _ & X37 & X38 & X39 & X40 & X41).
fold E in X32, X33, X37, X38, X39, X40, X41.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; exact (ew_Ereg_nat regs _ n r Hn)).
assert (Hpp8 : pp mod 8 = 0) by (apply wmod16_8; exact Hpp16).
assert (Hsh4 : shadow_addr (pp + 0x4000) = shadow_addr pp + 2048) by (rewrite wshadow_pp_L by (try lia; reflexivity); reflexivity).
assert (U9 : bv_unsigned (ew E 9) = R) by (rewrite (EE 9%nat 9%bv eq_refl), H9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = shadow_addr pp + 2048) by (rewrite (EE 20%nat 20%bv eq_refl), H20, Hsh4; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = pp + 0x4000) by (rewrite (EE 21%nat 21%bv eq_refl), H21; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite (EE 23%nat 23%bv eq_refl), H23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = pp) by (rewrite (EE 27%nat 27%bv eq_refl), H27; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = Model.pad8 sz) by (rewrite (EE 24%nat 24%bv eq_refl), H24; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E A_F) = F) by (rewrite X32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E A_L) = L) by (rewrite X33; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E A_SZ) = sz) by (rewrite X37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E A_FS) = 1) by (rewrite X38; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E A_KK) = kk) by (rewrite X39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E A_CNT) = cnt) by (rewrite X40; apply unsigned_lit_small; lia).
assert (U41 : bv_unsigned (ew E A_NE) = ne) by (rewrite X41; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ssC1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W_C) mem (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC1. apply (entry_st_ok_full rsegs). all: fold E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [ | | | | apply Forall_nil].
    + apply (rok_slots E _ mem R F pp 1 kk cnt U9 U27 U32 U38 U39 U40 HSL); lia.
    + apply (rok_len E _ mem pp _ (L + 8 + sz) U21); [ | exact HLEN | lia | | lia | lia].
      * unfold len_C. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
        rewrite (wU_off E A_L 8 L U33), (wU_off0 E A_SZ sz U37) by lia.
        apply zcanon_id. unfold M64. lia.
      * intros i Hi. replace (pp + 0x4000 + i) with (pp + (0x4000 + i)) by lia. apply HWR. lia.
    + apply (rok_sh4 E _ mem pp U20 HSH); lia.
    + apply (rok_ne E _ mem pp ne U27 U41 HNE); [lia | | lia | lia].
      intros i Hi. replace (pp + 0x4d14 + i) with (pp + (0x4d14 + i)) by lia. apply HWR. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val r_slots r_lenv r_sh4 r_ne].
    rewrite U9, U21, U20, U27. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct Hz as [Hz|Hz]; repeat split; lia.
  - split; [|split].
    + cbn [f_atoms fC atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U27, U33, U37, U24, U38, U39, U40, U41.
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      repeat split; lia.
    + exact I.
    + cbn [f_alias alias_ok]. split; [| exact I]. apply (w_al_ne_ok E pp U27 U23 U20 Hpp8); lia. }
unfold cfg_at. change (w64 W_C) with (Z_to_bv 64 W_C).
aj_run wtbl_ok HS HJ.
- lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?ow =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 ow) end.
  assert (Haw : forall a, pp <= a < pp + Layout.PP_SIZE ->
    awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly2 S2) ly2 own a).
  { intros a Ha. replace a with (pp + (a - pp)) by lia. apply (rl_fresh_awr _ _ _ _ _ _ _ pp Layout.PP_SIZE); [exact Hin | exact Hfr |].
    unfold req_size, Layout.PP_SIZE in *. cbn. lia. }
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn; lia|]
  | eapply awr_ok_cons_gen; [reflexivity | eassumption | intros a Ha; apply Haw; unfold Layout.PP_SIZE; cbn [YP09.r_wlo YP09.r_whi] in Ha; lia |] ].
- lazymatch goal with
  | HS1 : st_ok _ _ ?ssf (restrict _ ?msf), HJ1 : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdf _,
    HFr1 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    apply SRr_ret; split; [reflexivity|];
    exists (ms_regs msf), (ms_mem msf), mdf;
    rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ msf HS1 eq_refl) at 1;
    rename HS1 into HSf, HJ1 into HJf, HFr1 into HFrf
  end.
  lazymatch type of HSf with st_ok _ _ ?ssf ?msf =>
    let rl := eval vm_compute in (nth 1 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    let rn := eval vm_compute in (nth 3 (ss_mem ssf) (YP09.mkRegion None 0 0 0 0 [])) in
    assert (Inl : In rl (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]));
    assert (Inn : In rn (ss_mem ssf)) by (vm_compute; repeat (first [left; reflexivity | right]))
  end.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inl Hc) as CL.
  pose proof (fun c Hc => w_chunk_of _ _ _ _ c HSf Inn Hc) as CN.
  cbn [YP09.r_chunks YP09.r_base base_val ms_mem restrict] in CL, CN. rewrite U21 in CL. rewrite U27 in CN.
  assert (Q24 : bv_unsigned (ew E 24) = Model.pad8 sz) by exact U24.
  assert (Q33 : bv_unsigned (ew E 33) = L) by exact U33.
  assert (Q37 : bv_unsigned (ew E 37) = sz) by exact U37.
  assert (Q41 : bv_unsigned (ew E 41) = ne) by exact U41.
  split; [reflexivity|].
  split; [exact HJf|].
  split; [apply RPgCfgChanges.same_io_wvb|].
  split; [wreg HSf (1%bv : bv 5); reflexivity|].
  split; [wreg HSf (10%bv : bv 5); rewrite denot_lit_U; unfold w64; f_equal;
          rewrite U_SAlu, U_SMd, U_SLit; cbn [zalu_raw zmd_raw]; rewrite (wU_off E 27 16404 pp U27), (wU_off0 E 41 ne Q41) by lia;
          rewrite (zcanon_id 104) by (unfold M64; lia); rewrite (zcanon_id (ne * 104)) by (unfold M64; lia);
          rewrite zcanon_id by (unfold M64; lia); lia|].
  split; [wreg HSf (11%bv : bv 5); cbn [sv_denot]; rewrite (U32 : bv_unsigned (ew E 32) = F); reflexivity|].
  split; [wreg HSf (12%bv : bv 5); reflexivity|].
  split; [intros r Hr; exact (regs_kept_of_st_ok rsegs E _ _ regs _ wkeep HSf HAE ltac:(vm_compute; reflexivity) r Hr)|].
  split.
  { pose proof (CL _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk8 in C0. rewrite Z.add_0_r in C0.
    replace (L + 8 + sz + Model.pad8 sz) with (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 24 8) (SOff 33 0)) (SOff 37 0))); [exact C0|].
    rewrite !U_SAlu. cbn [zalu_raw]. rewrite (wU_off E 24 8 _ Q24), (wU_off0 E 33 L Q33), (wU_off0 E 37 sz Q37) by lia.
    rewrite (zcanon_id (Model.pad8 sz + 8 + L)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  split.
  { pose proof (CN _ ltac:(cbn; left; reflexivity)) as C0. apply w_chunk4v in C0.
    replace (ne + 1) with (U E (SOff 41 1)); [exact C0|]. apply (wU_off E 41 1 ne Q41). lia. }
  intros a Ha H1 H2. apply aview_eq_of. apply HFrf. rewrite unsigned_lit_small by exact Ha.
  intros (r & Hr & Hw). unfold ssC1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val r_slots r_lenv r_sh4 r_ne] in Hw; try lia.
Qed.
End w.
