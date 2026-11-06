(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 1310 of its 1364 lines of code are new or changed and 437 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacRateSnap.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_master_only_cadence_ns_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_master_only_cadence_ns.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import FpStep.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac mc_chain Wv Ev regsv memv Uspv HFrx Hold Hnew :=
  lazymatch type of HFrx with
  | frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem ?msx)) =>
    assert (Hnew : forall x : word, ~ (spZ regsv + -112 <= bv_unsigned x < spZ regsv) ->
      mrestrict (w_H Wv) (ms_mem msx) x = mrestrict (w_H Wv) memv x);
    [ intros x Hx; rewrite (HFrx x);
      [ apply Hold; exact Hx
      | intros (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Uspv in Hw; lia | ]);
        destruct Hr ]
    | ]
  end.
Ltac mc_chain_cur Wv Ev regsv memv Uspv Hold Hnew :=
  match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
    match goal with HFx : frame_of _ _ (mrestrict _ _) (mrestrict _ (ms_mem msc)) |- _ => mc_chain Wv Ev regsv memv Uspv HFx Hold Hnew end end.
Ltac mc_chainR regsv memv Uspv HFx Hold Hnew :=
  lazymatch type of HFx with
  | frame_of _ _ _ (ms_mem ?msx) =>
    assert (Hnew : forall x : word, ~ (spZ regsv + -112 <= bv_unsigned x < spZ regsv) -> ms_mem msx x = memv x);
    [ intros x Hx; rewrite (HFx x);
      [ apply Hold; exact Hx
      | intros (r & Hr & Hw);
        lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end;
        cbn [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?Uspv in Hw; lia | ]);
        destruct Hr ]
    | ]
  end.
Ltac mc_chainR_cur regsv memv Uspv Hold Hnew :=
  match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
    match goal with HFx : frame_of _ _ _ (ms_mem msc) |- _ => mc_chainR regsv memv Uspv HFx Hold Hnew end end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Definition mc_SB : Z := 0x7fff8000.
Definition mc_Bx : sv := SOff 32 0.
Definition mc_Bspan : Z * Z := (mc_SB, mc_SB + 2 ^ 44 - 1).
Definition mc_regions : smem := [stack_region 112; got_regionP; bcell_regionP 32].
Definition mc_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF mc_SB mc_SB 0); (A_OBJ 65, mkAF IMG_LO IMG_TOP 0) ] [] [].
Definition mc_ss0 : sstate := mkSS AF_reac_master_only_cadence_ns sr_atoms mc_regions None mc_facts.
Definition mc_SH : list shent := [ mkSHE (A_OBJ 65) 0 12 ].
Definition mc_E (regs : bvmap 5 word) (fv : word) : env := Eimg (Ereg regs [Z_to_bv 64 mc_SB; fv]).
Lemma mc_fetch : forall k w, plookup (@pl_tpi disco_listing PL_disco) k = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (BASE + k)) = Some (Z_to_bv 32 w).
Proof.
intros k w Hpl. rewrite <- pl_tpi_eq in Hpl.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert _ _ Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (BASE + k)) as [wz|] eqn:Hl; [|discriminate Hck].
apply Z.eqb_eq in Hck. subst wz. apply pa_fetch_ok. exact Hl.
Qed.
Lemma mc_pc4 : forall k k', k' = k + 4 -> 0 <= k < 2 ^ 40 ->
  v_addi (Z_to_bv 64 (BASE + k)) 4 = Z_to_bv 64 (BASE + k').
Proof.
intros k k' Hk' Hk. pose proof pa_B_ok as HB. unfold v_addi.
rewrite unsigned_lit_small by lia. f_equal. lia.
Qed.
Definition mc_bytes (v : Z) : list byte := map (fun k => Z_to_bv 8 (le_byte v 8 k)) (seq 0 8).
Lemma mc_rdn8 : forall m a v, val_mem SEGS m a 8 v -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (mc_bytes v).
Proof.
intros m a v H. apply (mbytes_at_rdn SEGS m a (mc_bytes v)).
intros j Hj. cbn [length mc_bytes map seq] in Hj.
destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; try lia; cbn [nth_error mc_bytes map seq]; apply H; lia.
Qed.
Lemma pa_code_top : forall k e, 0 <= k < 2 ^ 40 -> plookup pl_tpi k = Some e -> BASE + k < IMG_TOP.
Proof.
intros k e Hk40 Hk. rewrite <- pl_tpi_eq in Hk.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert k e Hk) as [Hc Hk0].
unfold pi_slot_check in Hc.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate].
pose proof (pa_tbl_ok _ _ Hf) as Hfw.
unfold fetch_word in Hfw. destruct (negb _); [discriminate|].
unfold code_read in Hfw.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k))) (Z.of_N 4)) as [sg|] eqn:Hfs; [|discriminate].
destruct (find_segment_hit _ _ _ _ Hfs) as (Hin & Hlo & Hhi).
assert (Himg : in_img SEGS (bv_unsigned (Z_to_bv 64 (VAL A_TEXT + k)))).
{ exists sg. split; [exact Hin|]. change (Z.of_N 4) with 4 in Hhi. lia. }
pose proof (pa_img_range _ Himg) as HR.
pose proof pa_B_ok as HB.
rewrite Z_to_bv_unsigned in HR. unfold bv_wrap in HR. change (bv_modulus 64) with (2 ^ 64) in HR.
rewrite Z.mod_small in HR by lia. lia.
Qed.
Lemma pa_hi_far : forall k j, 0 <= k < 2 ^ 40 -> (exists rd, plookup pl_tpi k = Some (PHi rd j)) ->
  VAL (A_HI j) < IMG_TOP + 2 ^ 31 \/ 2 ^ 64 - 2 ^ 31 <= VAL (A_HI j).
Proof.
intros k j Hk40 [rd Hpl].
pose proof (pa_code_top k _ Hk40 Hpl) as Htop.
pose proof (pa_slot_img k _ Hk40 Hpl) as Hlo.
rewrite <- pl_tpi_eq in Hpl.
pose proof (cert_slot dsym (clookup pa_tbl) VAL SIGMA disco_listing pa_cert _ _ Hpl) as (Hck & Hk0 & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|]; [|discriminate].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct i; try (rewrite Bool.andb_false_r in Hck; discriminate).
apply andb_prop in Hck as [_ Hck]. apply andb_prop in Hck as [_ Hck]. apply Z.eqb_eq in Hck.
rewrite <- Hck. unfold auipc_val, zcanon, M64.
pose proof (bv_signed_in_range _ (bv_concat 32 imm (Z_to_bv 12 0)) ltac:(discriminate)) as Hs.
change (bv_half_modulus 32) with (2 ^ 31) in Hs.
pose proof pa_B_ok as HB. unfold IMG_LO, IMG_TOP in *.
set (x := bv_signed (bv_concat 32 imm (Z_to_bv 12 0))) in *.
destruct (Z_le_gt_dec 0 (VAL A_TEXT + k + x)) as [Hp|Hn].
- left. rewrite Z.mod_small by lia. lia.
- right. replace ((VAL A_TEXT + k + x) mod 2 ^ 64) with (VAL A_TEXT + k + x + 2 ^ 64) by (apply Z.mod_unique with (q := -1); lia). lia.
Qed.
Lemma mc_keep_ro : forall (Bv : asyms) (Wv : world SEGS) (m m' : word -> option byte) (lo hi : Z),
  alloc_ceiling <= lo ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> mrestrict (w_H Wv) m' x = mrestrict (w_H Wv) m x) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi Bv (aview SEGS (w_H Wv) m) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi Bv (aview SEGS (w_H Wv) m').
Proof.
intros Bv Wv m m' lo hi Hlo Hkeep HRO a Hro Hown Herr.
assert (Harange : 0 <= a < alloc_ceiling).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hrel];
  [ pose proof (pa_segs_low a (ex_intro _ sg (conj Hin Hr)))
  | pose proof (pa_segs_low a (pa_relro_img a Hrel)) ];
  pose proof (proj1 asan_consts); unfold kLowMemEnd in *; lia. }
unfold aview, mbyte in *. rewrite Hkeep.
- exact (HRO a Hro Hown Herr).
- rewrite unsigned_lit_small by (pose proof (proj1 asan_consts); lia). lia.
Qed.
Lemma mc_keep_val : forall (m m' : word -> option byte) (lo hi : Z) a n v,
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall k, (k < n)%nat -> ~ (lo <= (a + Z.of_nat k) mod 2 ^ 64 < hi)) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof.
intros m m' lo hi a n v Hkeep Hout H k Hk.
unfold mbyte. rewrite Hkeep.
- exact (H k Hk).
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Hout. exact Hk.
Qed.
Lemma mc_keep_garr8 : forall (m m' : word -> option byte) (lo hi : Z) a (L : list Z),
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> m' x = m x) ->
  (forall k, (k < length L)%nat -> ~ (lo <= (a + Z.of_nat k) mod 2 ^ 64 < hi)) ->
  garr8 SEGS m a L -> garr8 SEGS m' a L.
Proof.
intros m m' lo hi a L Hkeep Hout H j Hj.
destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
eapply (mc_keep_val m m' lo hi _ 1 _ Hkeep); [| exact Hv].
intros k Hk. replace (a + Z.of_nat j + Z.of_nat k) with (a + Z.of_nat j) by (destruct k; [lia | lia]).
apply Hout. exact Hj.
Qed.
Lemma mc_shok_env : forall E1 E2 (m : word -> option byte),
  ew E2 32 = ew E1 32 -> ew E2 (A_OBJ 65) = ew E1 (A_OBJ 65) ->
  YCbn.sh_ok SEGS mc_Bx mc_SH E1 m -> YCbn.sh_ok SEGS mc_Bx mc_SH E2 m.
Proof.
intros E1 E2 m H32 H65 HSH.
assert (HB : U E2 mc_Bx = U E1 mc_Bx) by (unfold U, mc_Bx; cbn [sv_denot]; rewrite H32; reflexivity).
assert (HO : U E2 (SOff (A_OBJ 65) 0) = U E1 (SOff (A_OBJ 65) 0)) by (unfold U; cbn [sv_denot]; rewrite H65; reflexivity).
unfold YCbn.sh_ok, mc_SH in *. inversion HSH as [|e l He Hrest Heq]. subst.
constructor; [|constructor].
destruct He as [Hra Happ]. unfold YCbn.shent_ok. cbn [she_m she_lo she_hi] in *.
split.
- rewrite HB, HO. exact Hra.
- unfold YCbn.app_apart in *. cbn [she_m she_lo she_hi] in *. rewrite HB, HO. exact Happ.
Qed.
Lemma mc_region_kept_refl : forall E0 (m : word -> option byte) r, region_kept SEGS E0 m m r.
Proof. intros E0 m r. split; intros a Ha; [reflexivity | intros Hw; exact Hw]. Qed.
Lemma mc_fs0_rdn : forall E0 (m : word -> option byte) n lo hi wlo whi cs b (v : sv) (fvv : word),
  region_ok SEGS E0 m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E0 n) = b -> In (YP09.mkChunk (-112) (CVal 8 v)) cs -> sv_denot E0 v = fvv ->
  rdn SEGS m (Z_to_bv 64 (b + -112)) 8 = Some (word_to_le_bytes 8 fvv).
Proof.
intros E0 m n lo hi wlo whi cs b v fvv (_ & _ & _ & Hcs) Hb Hin Hv.
cbn [YP09.r_base YP09.r_chunks base_val] in Hcs. rewrite Hb in Hcs.
rewrite Forall_forall in Hcs. pose proof (Hcs _ Hin) as Hc.
assert (HL : length (word_to_le_bytes 8 fvv) = 8%nat) by apply length_N_to_le_bytes.
rewrite <- HL. apply mbytes_at_rdn. intros j Hj. rewrite HL in Hj.
destruct (Hc (Z.of_nat j) ltac:(cbv [YP09.c_len YP09.c_val cv_len]; cbn; lia)) as (bb & Hcb & Hmb).
cbn [YP09.c_off YP09.c_val] in Hcb, Hmb.
replace (b + -112 + Z.of_nat j) with (b + -112 + Z.of_nat j) by reflexivity.
rewrite Hmb. rewrite <- Hcb.
change 8%N with (N.of_nat 8). rewrite st_bytes_cbyte by lia. rewrite Hv, Nat2Z.id.
unfold word_to_le_bytes. rewrite Z_to_le_bytes_st. reflexivity.
Qed.
Lemma mc_word_rt : forall v : word, bv_extract 0 64 (le_bytes_to_word (word_to_le_bytes 8 v)) = v.
Proof.
intros v. rewrite le_bytes_to_word_Z, bytes_le_to_Z_8, Z_to_bv_bv_unsigned.
apply bv_eq. rewrite bv_extract_unsigned, Z.shiftr_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Definition mc_ke (F G : bvmap 5 word) : Prop :=
  forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 ->
  Sem.reg_get G k = Sem.reg_get F k.
Lemma mc_ke_refl : forall F, mc_ke F F.
Proof. intros F k _ _ _ _. reflexivity. Qed.
Lemma mc_ke_set : forall F G (j : bv 5) v,
  existsb (Z.eqb (bv_unsigned j)) [8; 10; 14; 15] = true -> mc_ke F G -> mc_ke F (bvmap_set j v G).
Proof.
intros F G j v Hj H k H8 H10 H14 H15.
cbn [existsb] in Hj.
rewrite fp_rg_other; [apply H; assumption|].
destruct (Z.eqb_spec (bv_unsigned j) 8); [lia|].
destruct (Z.eqb_spec (bv_unsigned j) 10); [lia|].
destruct (Z.eqb_spec (bv_unsigned j) 14); [lia|].
destruct (Z.eqb_spec (bv_unsigned j) 15); [lia|].
discriminate Hj.
Qed.
Lemma mc_ke_fin : forall F G, mc_ke F G -> freg_kept F (bvmap_set (Z_to_bv 5 8) (Sem.reg_get F (Z_to_bv 5 8)) G).
Proof.
intros F G H k H10 H14 H15.
destruct (Z.eq_dec (bv_unsigned k) 8) as [E8|E8].
- replace k with (Z_to_bv 5 8) by (apply bv_eq; rewrite E8; reflexivity). apply fp_rg_same.
- rewrite fp_rg_other by (change (bv_unsigned (Z_to_bv 5 8)) with 8; lia). apply H; assumption.
Qed.
Ltac mc_ke_tac := apply mc_ke_fin; repeat (apply mc_ke_set; [vm_compute; reflexivity | ]); apply mc_ke_refl.
(* rate_snap's post now names its final FP state only up to apost_base's two FP clauses: every f-register but f10
   as rate_snap's own clause sets them, and the csr as it computes it or with a zero rounding-mode field. *)
Lemma mc_ke_call : forall F H G' a b,
  (forall k : bv 5, bv_unsigned k <> 10 ->
     Sem.reg_get G' k = Sem.reg_get (bvmap_set (Z_to_bv 5 14) a (bvmap_set (Z_to_bv 5 15) b H)) k) ->
  mc_ke F H -> mc_ke F G'.
Proof.
intros F H G' a b HG HK k H8 H10 H14 H15. rewrite (HG k H10).
rewrite fp_rg_other by (change (bv_unsigned (Z_to_bv 5 14)) with 14; lia).
rewrite fp_rg_other by (change (bv_unsigned (Z_to_bv 5 15)) with 15; lia).
apply HK; assumption.
Qed.
Lemma mc_csr_trans : forall a b c : bv 32,
  (b = a \/ Z.land (Z.shiftr (bv_unsigned b) 5) 7 = 0) -> (c = b \/ Z.land (Z.shiftr (bv_unsigned c) 5) 7 = 0) ->
  c = a \/ Z.land (Z.shiftr (bv_unsigned c) 5) 7 = 0.
Proof. intros a b c [-> | Hb] [-> | Hc]; auto. Qed.
Ltac mc_ke_go := first [ apply mc_ke_refl | (apply mc_ke_set; [vm_compute; reflexivity | mc_ke_go])
                       | (eapply mc_ke_call; [eassumption | mc_ke_go]) ].
Ltac mc_byte H HL j :=
  match goal with |- mbyte ?s ?mm ?A = _ =>
    replace A with (VAL (A_OBJ 65) + Z.of_nat j + Z.of_nat 0) by lia end;
  rewrite (proj1 (H j ltac:(rewrite HL; lia)) 0%nat ltac:(lia)); f_equal; vm_compute; reflexivity.
Lemma mc_rates_val : forall m,
  garr8 SEGS m (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS m (VAL (A_OBJ 65) + 0) 4 44100 /\ val_mem SEGS m (VAL (A_OBJ 65) + 4) 4 48000 /\
  val_mem SEGS m (VAL (A_OBJ 65) + 8) 4 96000.
Proof.
intros m H.
assert (HL : length (map (fun b : byte => bv_unsigned b) RATES) = 12%nat) by (vm_compute; reflexivity).
split; [|split]; intros k Hk; destruct k as [|[|[|[|k]]]]; try lia.
- mc_byte H HL 0%nat.
- mc_byte H HL 1%nat.
- mc_byte H HL 2%nat.
- mc_byte H HL 3%nat.
- mc_byte H HL 4%nat.
- mc_byte H HL 5%nat.
- mc_byte H HL 6%nat.
- mc_byte H HL 7%nat.
- mc_byte H HL 8%nat.
- mc_byte H HL 9%nat.
- mc_byte H HL 10%nat.
- mc_byte H HL 11%nat.
Qed.
Definition mc_rates : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 65)) 0 12 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit 44100)); YP09.mkChunk 4 (CVal 4 (SLit 48000)); YP09.mkChunk 8 (CVal 4 (SLit 96000))].
Lemma mc_rates_ok : forall E0 (m : word -> option byte),
  bv_unsigned (ew E0 (A_OBJ 65)) = VAL (A_OBJ 65) -> IMG_LO <= VAL (A_OBJ 65) -> VAL (A_OBJ 65) + 8 <= IMG_TOP ->
  garr8 SEGS m (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  region_ok SEGS E0 m mc_rates.
Proof.
intros E0 m Hb Hlo Hhi HR.
destruct (mc_rates_val m HR) as (V0 & V4 & V8).
unfold region_ok, mc_rates. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite Hb. unfold IMG_LO, IMG_TOP in *.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat constructor.
- apply (chunk_ok_val SEGS E0 m (VAL (A_OBJ 65)) 0 4 (SLit 44100) 44100); [reflexivity | cbn; lia | cbn; lia | exact V0].
- apply (chunk_ok_val SEGS E0 m (VAL (A_OBJ 65)) 4 4 (SLit 48000) 48000); [reflexivity | cbn; lia | cbn; lia | exact V4].
- apply (chunk_ok_val SEGS E0 m (VAL (A_OBJ 65)) 8 4 (SLit 96000) 96000); [reflexivity | cbn; lia | cbn; lia | exact V8].
Qed.
Lemma mc_keep_first : forall (fq0 : YK11.FPState) E0 pc sr r0 rest rv G ms,
  @st_ok_pi SEGS VAL fq0 E0 (mkSS pc sr (r0 :: rest) rv G) ms -> @st_ok_pi SEGS VAL fq0 E0 (mkSS pc sr [r0] rv G) ms.
Proof.
intros fq0 E0 pc sr r0 rest rv G ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9).
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [|exact H9].
change (regions_wf (r0 :: rest) = true) in Hwf.
change (Forall (region_ok SEGS E0 (ms_mem ms)) (r0 :: rest)) in Hok.
change (mem_ok SEGS E0 (ms_mem ms) [r0]).
assert (Hw : region_wf r0 = true) by (cbn [regions_wf] in Hwf; apply andb_prop in Hwf; tauto).
split; [cbn [regions_wf]; rewrite Hw; reflexivity|].
split; [inversion Hok; subst; constructor; [assumption | constructor]|].
cbn [pairwise_disjoint all_disjoint]. split; exact I.
Qed.
Lemma mc_shok_keep : forall E0 (m m' : word -> option byte),
  U E0 mc_Bx = mc_SB -> U E0 (SOff (A_OBJ 65) 0) = VAL (A_OBJ 65) ->
  IMG_LO <= VAL (A_OBJ 65) -> VAL (A_OBJ 65) + 8 <= IMG_TOP ->
  (forall a, mc_SB <= a < mc_SB + 2 ^ 44 -> mbyte SEGS m' a = mbyte SEGS m a) ->
  YCbn.sh_ok SEGS mc_Bx mc_SH E0 m -> YCbn.sh_ok SEGS mc_Bx mc_SH E0 m'.
Proof.
intros E0 m m' HB HO Hlo Hhi Hkeep HSH.
unfold YCbn.sh_ok, mc_SH in *. inversion HSH as [|e l He Hrest Heq]. subst.
constructor; [|constructor].
destruct He as [Hra Happ]. split; [|exact Happ].
cbn [she_m she_lo she_hi] in *. rewrite HB, HO in Hra |- *.
eapply range_addressable_agree; [|exact Hra].
intros x Hx. unfold YCbn.rd_of. f_equal. apply Hkeep.
unfold shadow_of_addr, mc_SB, IMG_LO, IMG_TOP in *.
split; [|].
- assert (0 <= x / 8) by (apply Z.div_pos; lia). lia.
- assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TRATE : treac_rate_snap_spec B.
Definition REAC_MASTER_ONLY_CADENCE_NS_STK : Z := 112 + REAC_RATE_SNAP_STK.
Definition treac_master_only_cadence_ns_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (10 ^ 9) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         W' = W /\ (forall a : word, ~ (spZ regs - REAC_MASTER_ONLY_CADENCE_NS_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)) W' c'.
Definition treac_master_only_cadence_ns_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (fps : Z),
  afn_pre SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 96) + -1628) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_reac_master_only_cadence_ns) regs mem md)
    (treac_master_only_cadence_ns_post fq regs ly S W mem md).
Lemma mc_entry : forall (fq : YK11.FPState) ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B (112 + ESTACK) ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  @st_ok_pi SEGS VAL fq (mc_E regs (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))) mc_ss0
    (restrict (w_H W) (@mkst fq regs (Z_to_bv 64 (BASE + AF_reac_master_only_cadence_ns)) mem (seg_rom SEGS)))
  /\ YCbn.sh_ok SEGS mc_Bx mc_SH (mc_E regs (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch HPRE HRA.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite (fp_spZ_upd regs (Z_to_bv 64 0) 8%bv ltac:(vm_compute; discriminate)) in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
pose proof (pa_obj_img 1 ltac:(cbv [disco_nobj]; lia)) as Hob1.
pose proof (pa_obj_img 66 ltac:(cbv [disco_nobj]; lia)) as Hob66.
pose proof (pa_obj_img 65 ltac:(cbv [disco_nobj]; lia)) as Hob65.
pose proof (pal_got_cell B TL) as Hgc.
set (E := mc_E regs (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mc_E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 mc_SB)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E241 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (unfold E, mc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E307 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66)))
  by (unfold E, mc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E306 : ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (unfold E, mc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (Hsp : 2 ^ 46 <= spZ regs <= 2 ^ 47) by (unfold IMG_LO, IMG_TOP in *; lia).
rewrite restrict_mkst_fx. split.
- unfold mc_ss0. apply pa_entry_st_ok_full.
  + unfold E, mc_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold mc_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold ESTACK in *. lia.
    * cbn [base_val]. rewrite E241, unsigned_lit_small by (unfold IMG_LO, IMG_TOP in *; lia).
      split; [unfold IMG_LO in *; lia|]. split; [unfold IMG_TOP in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
      [cbn [sv_denot]; rewrite E307, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold IMG_LO, IMG_TOP in *; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * cbn [base_val]. rewrite E307, unsigned_lit_small by (unfold IMG_LO, IMG_TOP in *; lia).
      split; [unfold IMG_LO in *; lia|]. split; [unfold IMG_TOP in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) mc_SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold mc_SB; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  + apply pairwise_disjoint_of_extents. unfold mc_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, E241, E307.
    rewrite (unsigned_lit_small (VAL (A_OBJ 1))) by (unfold IMG_LO, IMG_TOP in *; lia).
    rewrite (unsigned_lit_small (VAL (A_OBJ 66))) by (unfold IMG_LO, IMG_TOP in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold IMG_LO, IMG_TOP in *. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [mc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, E306.
    rewrite (unsigned_lit_small mc_SB) by (unfold mc_SB; lia).
    rewrite (unsigned_lit_small (VAL (A_OBJ 65))) by (unfold IMG_LO, IMG_TOP in *; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold IMG_LO, IMG_TOP in *. repeat split; try lia.
- assert (HB : U E mc_Bx = mc_SB).
  { unfold U, mc_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold mc_SB. lia. }
  assert (HO : U E (SOff (A_OBJ 65) 0) = VAL (A_OBJ 65)).
  { unfold U. cbn [sv_denot]. rewrite E306, Z.add_0_r, Z_to_bv_bv_unsigned.
    apply unsigned_lit_small. unfold IMG_LO, IMG_TOP in *. lia. }
  unfold YCbn.sh_ok, mc_SH. constructor; [|constructor].
  unfold YCbn.shent_ok, YCbn.app_apart. cbn [she_m she_lo she_hi].
  rewrite HB, HO. replace (12 - 0) with 12 by lia. rewrite Z.add_0_r. split.
  + unfold mc_SB. exact HRA.
  + intros a Ha. unfold mc_SB, IMG_LO, IMG_TOP in *. lia.
Qed.
Lemma mc_call_rate : forall (fqx : YK11.FPState) (W : world SEGS) E ssx ms md Q STK sp0 ly S W0 mem0 md0 own lyc Sc k o retk,
  st_ok (fx := fqx) SEGS E (setpc ssx (SIGMA DS_reac_rate_snap)) (restrict (w_H W) ms) ->
  ss_resv ssx = None ->
  ajournal SEGS B STK sp0 [] ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  spZ (ms_regs ms) = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem ms)) ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (VAL (A_HI 97) + -1832) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (VAL (A_HI 96) + -1628) 8 D3837 ->
  (forall (fq' : YK11.FPState) ly2 S2 regs2 mem2 md2,
     (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs fq') k =
        Sem.reg_get (bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837) (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) (@YK11.fp_regs fqx))) k) ->
     (@YK11.fp_csr fq' = reac_rate_snap_fcsr (Sem.reg_get (@YK11.fp_regs fqx) (Z_to_bv 5 10)) (@YK11.fp_csr fqx) \/
      Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fq')) 5) 7 = 0) ->
     ajournal SEGS B STK sp0 [] ly S W0 mem0 md0 own ly2 S2 W mem2 md2 k ->
     aregs_preserved (ms_regs ms) regs2 ->
     getr regs2 10 = w64 (reac_rate_snap_model (Sem.reg_get (@YK11.fp_regs fqx) (Z_to_bv 5 10))) ->
     Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
     mem2 = ms_mem ms ->
     SRr SEGS W (mkCfg (@mkst fq' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros fqx W E ssx ms md Q STK sp0 ly S W0 mem0 md0 own lyc Sc k o retk
  HS Hrv HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hretk Hret2 HRO H6000 H3837 HK.
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
rewrite (st_ok_restrict_mkst SEGS (w_H W) E _ ms HS ltac:(destruct ssx; exact Hrv)).
cbn [ss_pc setpc].
rewrite (pa_sigma_reac_rate_snap (L := disco_listing)).
eapply SRr_bind.
{ eapply (TRATE fqx lyc Sc W (ms_regs ms) (ms_mem ms) md (@nil (Z * Z * Z))).
  - assert (Hupd : forall r : bv 5, bv_unsigned r <> 8 ->
      getr (regupd (ms_regs ms) (Z_to_bv 5 8) (Z_to_bv 64 0)) r = getr (ms_regs ms) r).
    { intros r Hr. apply fp_getr_upd. replace (bv_unsigned (Z_to_bv 5 8)) with 8 by (vm_compute; reflexivity). exact Hr. }
    assert (Hs0 : getr (regupd (ms_regs ms) (Z_to_bv 5 8) (Z_to_bv 64 0)) 8 = Z_to_bv 64 0).
    { replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; vm_compute; reflexivity).
      apply getr_same. intros X. vm_compute in X. discriminate. }
    eapply (afn_pre_at SEGS B STK sp0 (@nil (Z * Z)) ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k
      (regupd (ms_regs ms) (Z_to_bv 5 8) (Z_to_bv 64 0)) ESTACK o (@nil (Z * Z * Z)) HJ).
    + unfold spZ. rewrite Hupd by (vm_compute; discriminate). exact Hsp.
    + exact Hal.
    + exact Hneg.
    + unfold ESTACK; lia.
    + exact Hbud.
    + rewrite Hupd by (vm_compute; discriminate).
      rewrite Hra. apply ret_ok_codeptr_v; [exact Hretk | exact Hret2].
    + unfold raZ. rewrite Hupd by (vm_compute; discriminate).
      rewrite Hra, unsigned_lit_small.
      * pose proof (pa_base_lo (PL := PL_disco)) as Hlo. unfold IMG_LO in Hlo. lia.
      * pose proof pa_B_ok as HB. lia.
    + rewrite Hupd by (vm_compute; discriminate). exact Hgp.
    + rewrite Hupd by (vm_compute; discriminate). exact Htp.
    + apply achain_low. unfold s0Z. rewrite Hs0.
      pose proof (proj1 asan_consts). vm_compute (bv_unsigned (Z_to_bv 64 0)). lia.
  - exact HRO.
  - exact H6000.
  - exact H3837. }
cbv beta. intros W2 c2 _ (fqo & Hfr' & Hfc' & fq' & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfr2 & Hfc2 & HJ1 & HP2 & Ha0 & Hperm & -> & Hmem2).
rewrite Hfr' in Hfr2. rewrite Hfc' in Hfc2.
rewrite Hra. eapply HK; try eassumption.
- replace k with (k + 0) by lia.
  change own with (@nil (Z * Z) ++ own).
  rewrite Hsp in HJ1.
  eapply (ajournal_sub SEGS B LAWS pa_segs_low).
  + exact HJ.
  + exact HJ1.
  + unfold REAC_RATE_SNAP_STK. unfold ESTACK in *. lia.
  + lia.
  + intros a Ha. exfalso. destruct Ha as (r0 & Hr0 & _). destruct Hr0.
- apply functional_extensionality. exact Hmem2.
Qed.
Theorem pb_reac_master_only_cadence_ns : treac_master_only_cadence_ns_spec.
Proof.
unfold treac_master_only_cadence_ns_spec.
intros fq ly S W regs mem md ch fps HPRE HRO H10 Hfps HRA HRATES H6000 H3837.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK in *.
destruct (mc_entry fq ly S W regs mem md ch HPRE HRA) as [HS SHOK].
fold (mc_E regs (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))) in HS, SHOK.
pose proof (ajournal_init SEGS B (112 + ESTACK) [] ly S W _ mem md ch HPRE) as HJ.
rewrite (fp_spZ_upd regs (Z_to_bv 64 0) 8%bv ltac:(vm_compute; discriminate)) in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite (fp_spZ_upd regs (Z_to_bv 64 0) 8%bv ltac:(vm_compute; discriminate)) in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
set (E := mc_E regs (Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mc_E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 fps)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E3 : ew E 3 = getr regs 3)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (Hgp' : getr regs 3 = w64 (as_gp B))
  by (rewrite <- Hgp; symmetry; apply fp_getr_upd; vm_compute; discriminate).
assert (Htp' : getr regs 4 = w64 (as_tp B))
  by (rewrite <- Htp; symmetry; apply fp_getr_upd; vm_compute; discriminate).
assert (Hsg : bv_signed (Z_to_bv 64 fps) = fps).
{ rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). change (bv_half_modulus 64) with (2 ^ 63).
  rewrite Z.mod_small by lia. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 mc_SB)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E306 : ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (unfold E, mc_E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 65 ltac:(cbv [disco_nobj]; lia)) as Hob65.
assert (Hpl96 : plookup (@pl_tpi disco_listing PL_disco) 31472 = Some (PHi (10%bv : bv 5) 96)) by (vm_compute; reflexivity).
assert (Hpl97 : plookup (@pl_tpi disco_listing PL_disco) 31476 = Some (PHi (11%bv : bv 5) 97)) by (vm_compute; reflexivity).
assert (Hout96 : forall k, (k < 8)%nat -> ~ (spZ regs + -112 <= (VAL (A_HI 96) + -1628 + Z.of_nat k) mod 2 ^ 64 < spZ regs)).
{ pose proof (pa_hi_far 31472 96 ltac:(clear; lia) (ex_intro _ _ Hpl96)) as Hf.
  pose proof (pa_val_range (A_HI 96)) as Hv. intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < 8) by lia.
  clear - Hf Hv Hk' Hceil Hslo Hshi H47 C1. unfold IMG_TOP, ESTACK in *. set (z := Z.of_nat k) in *.
  destruct Hf as [Hf | Hf]; [destruct (Z_lt_le_dec (VAL (A_HI 96) + -1628 + z) 0) |].
  - rewrite <- (Z.mod_unique (VAL (A_HI 96) + -1628 + z) (2 ^ 64) (-1) (VAL (A_HI 96) + -1628 + z + 2 ^ 64)) by lia. lia.
  - rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
assert (Hout97 : forall k, (k < 8)%nat -> ~ (spZ regs + -112 <= (VAL (A_HI 97) + -1832 + Z.of_nat k) mod 2 ^ 64 < spZ regs)).
{ pose proof (pa_hi_far 31476 97 ltac:(clear; lia) (ex_intro _ _ Hpl97)) as Hf.
  pose proof (pa_val_range (A_HI 97)) as Hv. intros k Hk.
  assert (Hk' : 0 <= Z.of_nat k < 8) by lia.
  clear - Hf Hv Hk' Hceil Hslo Hshi H47 C1. unfold IMG_TOP, ESTACK in *. set (z := Z.of_nat k) in *.
  destruct Hf as [Hf | Hf]; [destruct (Z_lt_le_dec (VAL (A_HI 97) + -1832 + z) 0) |].
  - rewrite <- (Z.mod_unique (VAL (A_HI 97) + -1832 + z) (2 ^ 64) (-1) (VAL (A_HI 97) + -1832 + z + 2 ^ 64)) by lia. lia.
  - rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia. }
clear Hpl96 Hpl97.
rewrite (fp_getr_upd regs (Z_to_bv 64 0) 8%bv 1%bv ltac:(vm_compute; discriminate)) in Hra.
unfold YK0s.ret_ok in Hra.
assert (E1 : ew E 1 = getr regs 1)
  by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 mc_SB; Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8)]) E)
  by (unfold E, mc_E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HBv : U E mc_Bx = mc_SB).
{ unfold U, mc_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold mc_SB. lia. }
assert (HOv : U E (SOff (A_OBJ 65) 0) = VAL (A_OBJ 65)).
{ unfold U. cbn [sv_denot]. rewrite E306, Z.add_0_r, Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold IMG_LO, IMG_TOP in *. lia. }
unfold cfg_at.
change (w64 (BASE + AF_reac_master_only_cadence_ns)) with (Z_to_bv 64 (BASE + AF_reac_master_only_cadence_ns)).
pose proof (paj_run (fx := fq) B LAWS) as RUN0.
paj_run_tok RUN0 HS HJ SHOK mc_Bspan.
- awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
- assert (HK0 : forall x : word, ~ (spZ regs + -112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) mem x = mrestrict (w_H W) mem x) by (intros; reflexivity).
  mc_chain W E regs mem Usp HFr HK0 HK1.
  assert (HR0 : forall x : word, ~ (spZ regs + -112 <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
  mc_chainR regs mem Usp HF HR0 HR1.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E _ ms HS eq_refl) as Hshape. cbn [ss_pc] in Hshape.
  prreg HS (Z_to_bv 5 2) R2.
  assert (E33 : ew E 33 = Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8))
    by (unfold E, mc_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  pose proof HS as HS0.
  lazymatch type of HS0 with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    destruct HS0 as (HF1 & HF2 & HF3 & HF4 & HF5 & HF6 & HRG & HMO & HFA);
    cbn [abs_ss setpc ss_pc ss_regs ss_mem ss_resv ss_facts restrict ms_mem ms_regs] in HMO, HRG, HFA;
    let r1 := eval vm_compute in (sstore (ss_mem ssx) (Some 2%nat) (-112) SZ8 (SOff 33 0)) in
    lazymatch r1 with
    | Some ?rs2 =>
      assert (Hsst : sstore (ss_mem ssx) (Some 2%nat) (-112) SZ8 (SOff 33 0) = Some rs2) by (vm_compute; reflexivity)
    | None => fail
    end
  end.
  destruct (YP09.sstore_sound SEGS E (mrestrict (w_H W) (ms_mem ms)) _ _ _ _ _ _ HMO Hsst) as [Hstore HMO2].
  cbn [base_val nbytes] in Hstore, HMO2.
  rewrite Usp in Hstore, HMO2.
  set (fv := Sem.reg_get (@YK11.fp_regs fq) (Z_to_bv 5 8)) in *.
  assert (Hbytes : st_bytes 8 (sv_denot E (SOff 33 0)) = word_to_le_bytes 8 fv).
  { cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. symmetry. apply Z_to_le_bytes_st. }
  rewrite Hbytes in HMO2.
  assert (Hstep0 : RiscvSemantics.step SEGS (@mkst fq (ms_regs ms) (Z_to_bv 64 (BASE + 33124)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) =
      MachineOk (@mkst fq (ms_regs ms) (Z_to_bv 64 (BASE + 33128))
        (wbytes (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (spZ regs + -112)) (word_to_le_bytes 8 fv)) (seg_rom SEGS))).
  { rewrite <- (mc_pc4 33124 33128 eq_refl ltac:(lia)).
    apply (fp_step_fsd fq SEGS (ms_regs ms) (Z_to_bv 64 (BASE + 33124)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)
             (Z_to_bv 32 8466471) (Z_to_bv 5 2) (Z_to_bv 5 8) (Z_to_bv 12 0) (Z_to_bv 64 (spZ regs + -112))).
    - apply mc_fetch. vm_compute. reflexivity.
    - vm_compute. reflexivity.
    - vm_refl_bv.
    - rewrite R2, Usp. replace (bv_signed (Z_to_bv 12 0)) with 0 by (vm_compute; reflexivity). unfold v_addi.
      rewrite unsigned_lit_small by lia. f_equal. lia.
    - exact Hstore. }
  assert (Hstep : RiscvSemantics.step SEGS (restrict (w_H W) ms) =
      MachineOk (@mkst fq (ms_regs ms) (Z_to_bv 64 (BASE + 33128))
        (wbytes (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (spZ regs + -112)) (word_to_le_bytes 8 fv)) (seg_rom SEGS)))
    by (rewrite Hshape at 1; rewrite restrict_mkst_fx; exact Hstep0).
  pose proof HJ as HJ0.
  pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  assert (Hhid : forall x : word, w_H W x = true -> ~ (spZ regs + -112 <= bv_unsigned x < spZ regs + -112 + 8)).
  { intros x Hx Hr. destruct (Hpres1 (bv_unsigned x) ltac:(unfold ESTACK in *; lia)) as [Hh _].
    rewrite Z_to_bv_bv_unsigned in Hh. rewrite Hx in Hh. discriminate. }
  assert (Hlen : length (word_to_le_bytes 8 fv) = 8%nat) by (apply length_N_to_le_bytes).
  assert (Hau : bv_unsigned (Z_to_bv 64 (spZ regs + -112)) = spZ regs + -112)
    by (apply unsigned_lit_small; unfold ESTACK in *; lia).
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssx _ =>
    let r1 := eval vm_compute in (sstore (ss_mem ssx) (Some 2%nat) (-112) SZ8 (SOff 33 0)) in
    lazymatch r1 with
    | Some ?rs1 =>
      eapply (fp_write_step SEGS B LAWS Hwx Hsegs fq W E (abs_ss VAL (mkSS 33128 (ss_regs ssx) rs1 None (ss_facts ssx))) ms _ _
        (112 + ESTACK) (spZ regs) (@nil (Z * Z)) ly S W mem md (@nil (Z * Z)) ly S 0
        (fun z => spZ regs + -112 <= z < spZ regs + -112 + 8) _ (Z_to_bv 64 (BASE + 33128)));
      [ exact HF3
      | exact HJ
      | exact Hstep
      | unfold st_ok; cbn [abs_ss setpc mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem
          ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts resv_denot];
        split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
        split; [reflexivity|]; split; [reflexivity|]; split; [exact HRG|]; split; [exact HMO2 | exact HFA]
      | intros x Hx; pose proof (Hhid x Hx) as Hout;
        destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -112)) as [Hlt|Hge];
        [ rewrite (wbytes_below (word_to_le_bytes 8 fv) _ _ x)
            by (rewrite ?Hlen, ?Hau; pose proof (bv_unsigned_in_range 64 x); unfold ESTACK in *; lia)
        | rewrite (wbytes_above (word_to_le_bytes 8 fv) _ _ x) by (rewrite ?Hlen, ?Hau; lia) ];
        unfold mrestrict; rewrite Hx; reflexivity
      | intros x Hx; destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -112)) as [Hlt|Hge];
        [ apply wbytes_below; [rewrite ?Hlen, ?Hau; pose proof (bv_unsigned_in_range 64 x); unfold ESTACK in *; lia | rewrite ?Hau; lia]
        | apply wbytes_above; rewrite ?Hlen, ?Hau; lia ]
      | apply wbytes_grows
      | intros a Ha; left; unfold ESTACK in *; lia
      | ]
    end
  end.
  intros ms1 mat1 Hregs1 Hmem1 Hhid1 HS1 HJ1.
  assert (SHOK1 : YCbn.sh_ok SEGS mc_Bx mc_SH E (mrestrict (w_H W) (ms_mem ms1))).
  { rewrite Hmem1. refine (mc_shok_keep E _ _ HBv HOv (proj1 Hob65) (proj2 Hob65) _ SHOK).
    intros a Ha. unfold mbyte.
    assert (Hau2 : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; unfold mc_SB in *; lia).
    rewrite (wbytes_below (word_to_le_bytes 8 fv) (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (spZ regs + -112)) (Z_to_bv 64 a));
      [ reflexivity
      | rewrite Hlen, Hau; unfold ESTACK in *; lia
      | rewrite Hau, Hau2; unfold mc_SB, ESTACK in *; lia ]. }
  assert (HK2 : forall x : word, ~ (spZ regs + -112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite Hmem1.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -112)) as [Hlt|Hge].
    - rewrite (wbytes_below (word_to_le_bytes 8 fv) _ _ x);
        [ apply HK1; exact Hx
        | rewrite Hlen, Hau; unfold ESTACK in *; lia
        | rewrite Hau; lia ].
    - rewrite (wbytes_above (word_to_le_bytes 8 fv) _ _ x);
        [ apply HK1; exact Hx | rewrite Hlen, Hau; lia ]. }
  assert (HR2 : forall x : word, ~ (spZ regs + -112 <= bv_unsigned x < spZ regs) -> ms_mem ms1 x = mem x).
  { intros x Hx. destruct (w_H W x) eqn:Hh.
    - rewrite (Hhid1 x Hh). apply HR1. exact Hx.
    - pose proof (HK2 x Hx) as Hk. unfold mrestrict in Hk. rewrite Hh in Hk. exact Hk. }
  lazymatch type of HS1 with
  | st_ok _ _ (abs_ss _ ?ssy) ?msy =>
    let s' := eval vm_compute in ssy in
    assert (HS2 : st_ok_pi SEGS VAL E s' msy) by exact HS1; clear HS1
  end.
  clear HMO HMO2 HF1 HF2 HF3 HF4 HF5 HF6 HRG HFA Hstep Hstep0 Hshape R2 Hsst Hstore HS SHOK HJ.
  paj_run_tok RUN0 HS2 HJ1 SHOK1 mc_Bspan.
  + awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
  + mc_chain W E regs mem Usp HFr0 HK2 HK3.
    mc_chainR regs mem Usp HF0 HR2 HR3.
    pose proof (paj_branch (fx := fq) (PI := PI)) as BR0.
    psrr_branch_tok RUN0 BR0 HS2 SHOK1 mc_Bspan.
    *
      paj_run_tok RUN0 HS2 HJ1 SHOK1 mc_Bspan.
      -- awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
      -- mc_chain W E regs mem Usp HFr1 HK3 HK4.
         mc_chainR regs mem Usp HF1 HR3 HR4.
         lazymatch type of HS2 with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HS2 end.
         pose proof (mc_keep_first _ _ _ _ _ _ _ _ _ HS2) as HSa. clear HS2.
         assert (HRn : garr8 SEGS (mrestrict (w_H W) (ms_mem ms2)) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES)).
         { apply (mc_keep_garr8 _ _ (spZ regs + -112) (spZ regs) _ _ HK4); [| exact HRATES].
           intros k Hk. replace (length (map (fun b : byte => bv_unsigned b) RATES)) with 12%nat in Hk by (vm_compute; reflexivity).
           assert (Hk' : 0 <= Z.of_nat k < 12) by lia.
           rewrite Z.mod_small by (unfold IMG_LO, IMG_TOP in *; lia).
           clear - Hk' Hob65 Hceil Hslo Hshi H47 C1. unfold IMG_LO, IMG_TOP, ESTACK in *. lia. }
         pose proof (st_ok_pi_add_region E _ _ mc_rates HSa ltac:(vm_compute; reflexivity)) as HSb.
         specialize (HSb ltac:(cbn [restrict ms_mem]; apply (mc_rates_ok E _ ltac:(rewrite E306; apply unsigned_lit_small; unfold IMG_LO, IMG_TOP in *; lia) (proj1 Hob65) (proj2 Hob65) HRn))).
         match type of HSb with ?P -> _ => assert (HD : P); [ | specialize (HSb HD); clear HD] end.
         { cbn [all_disjoint ss_mem]. split; [|exact I].
           unfold extent_disjoint, mc_rates. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
           assert (E306n : ew E 306 = Z_to_bv 64 (VAL (A_OBJ 65))) by exact E306.
           rewrite ?E306n, ?E306, Usp, unsigned_lit_small by (unfold IMG_LO, IMG_TOP in *; lia).
           left. unfold IMG_LO, IMG_TOP, ESTACK in *. lia. }
         clear HSa.
         lazymatch type of HSb with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HSb end.
         pose proof (paj_run (fx := fq) B LAWS) as RUNL.
         paj_run_tok RUNL HSb HJ1 SHOK1 mc_Bspan.
         ++ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
         ++ lazymatch type of HSb with st_ok_pi _ _ ?Ex _ _ => set (EC1 := Ex) in HSb, SHOK1 end.
            assert (EC1o : forall n, (n < 512)%nat -> ew EC1 n = ew E n) by (intros n Hn; unfold EC1; rewrite ?ew_ewset_other by lia; reflexivity).
            assert (HEIC1 : img_env VAL A_LIM EC1) by (unfold EC1; repeat (apply img_env_ewset_hi; [|unfold A_LIM; lia]); exact HEI).
            assert (UspC1 : bv_unsigned (ew EC1 2) = spZ regs) by (rewrite EC1o by lia; exact Usp).
            mc_chain_cur W EC1 regs mem UspC1 HK4 HKL1a.
            mc_chainR_cur regs mem UspC1 HR4 HRL1a.
            prreg HSb (Z_to_bv 5 10) R10L1.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              assert (Hu10L1 : bv_unsigned (getr (ms_regs msc) (Z_to_bv 5 10)) = 3675) by (rewrite R10L1; reflexivity);
              rewrite (st_ok_pi_restrict_mkst (w_H W) EC1 _ msc HSb eq_refl); cbn [ss_pc] end.
            destruct (reac_master_only_cadence_ns.cvt_ok 3675 ltac:(lia)) as (HflL1 & HrngL1 & HnanL1).
            set (XL1 := Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 3675))).
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
              assert (HstA1 : RiscvSemantics.step SEGS (@mkst fq Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)) =
                MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 10) XL1 (@YK11.fp_regs fq)) (@YK11.fp_csr fq)) Rc (Z_to_bv 64 (BASE + 33316)) (mrestrict (w_H W) Mc) (seg_rom SEGS)));
              [ rewrite <- (mc_pc4 33312 33316 eq_refl ltac:(lia));
                rewrite (fp_step_fcvt_d_wu fq SEGS Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)
                  (Z_to_bv 32 3524592979) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 3 0));
                [ rewrite Hu10L1, HflL1; change (fflags_bits no_flags) with 0; rewrite reac_master_only_cadence_ns.fcsr_keep; reflexivity
                | apply mc_fetch; vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv | vm_compute; reflexivity ]
              | ];
              eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with (f' := (mkFP (bvmap_set (Z_to_bv 5 10) XL1 (@YK11.fp_regs fq)) (@YK11.fp_csr fq))) (R' := Rc) (pc' := Z_to_bv 64 (BASE + 33316));
              [exact HstA1 | exact HJ1 | clear HJ1; intros mdA1 HJ1] end.
            pose proof HSb as HSc1. destruct HSc1 as (_ & _ & _ & _ & _ & _ & HRGc1 & _).
            cbn [abs_ss setpc ss_regs restrict ms_regs] in HRGc1.
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
            lazymatch type of HSb with
            | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
              pose proof (fp_switch SEGS fq (mkFP (bvmap_set (Z_to_bv 5 10) XL1 (@YK11.fp_regs fq)) (@YK11.fp_csr fq)) EC1 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) Rc (Z_to_bv 64 (BASE + 33316)) HSb HRGc1) as HSd1
            end end.
            cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HSd1.
            rewrite (unsigned_lit_small (BASE + 33316)) in HSd1 by (pose proof pa_B_ok as HB; lia).
            lazymatch type of HSd1 with
            | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
              assert (HSe1 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 10) XL1 (@YK11.fp_regs fq)) (@YK11.fp_csr fq)) EC1 (mkSS 33316 sr rs rv G) msy) by exact HSd1
            end.
            clear HSd1 HSb HRGc1 HstA1 R10L1.
            pose proof (paj_run (fx := (mkFP (bvmap_set (Z_to_bv 5 10) XL1 (@YK11.fp_regs fq)) (@YK11.fp_csr fq))) B LAWS) as RUNc1.
            cbn [ms_mem mkst] in SHOK1.
            paj_run_tok RUNc1 HSe1 HJ1 SHOK1 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspC1. }
            mc_chain_cur W EC1 regs mem UspC1 HKL1a HKL1b.
            mc_chainR_cur regs mem UspC1 HRL1a HRL1b.
            prreg HSe1 (2%bv : bv 5) Q2L1. prreg HSe1 (3%bv : bv 5) Q3L1. prreg HSe1 (4%bv : bv 5) Q4L1. prreg HSe1 (1%bv : bv 5) Q1L1.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              eapply (mc_call_rate _ W EC1 _ msc _ _ (112 + ESTACK) (spZ regs) ly S W mem md (@nil (Z * Z)) ly S 0 (-112) 33320 HSe1) end.
            { reflexivity. }
            { exact HJ1. }
            { unfold spZ at 1. rewrite Q2L1, UspC1. apply unsigned_lit_small. clear - Hceil Hslo Hshi H47 C1. unfold ESTACK in *. lia. }
            { reflexivity. }
            { lia. }
            { unfold ESTACK. lia. }
            { rewrite Q3L1, EC1o, E3 by lia. exact Hgp'. }
            { rewrite Q4L1, EC1o, E4 by lia. exact Htp'. }
            { exact Q1L1. }
            { lia. }
            { reflexivity. }
            { match goal with |- context [aview _ _ (ms_mem ?msc)] => apply (mc_keep_ro B W mem (ms_mem msc) (spZ regs + -112) (spZ regs)); [unfold ESTACK in *; lia | exact HKL1b | exact HRO] end. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL1b); [exact Hout97 | exact H6000]. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL1b); [exact Hout96 | exact H3837]. }
            intros fqL1 lyL1 SL1 regsL1 memL1 mdC1 HfrL1 HfcL1 HJL1 HPL1 Ha0L1 HpermL1 HmemL1. subst memL1.
            cbn [YK11.fp_regs YK11.fp_csr] in HfrL1, HfcL1, Ha0L1. rewrite fp_rg_same in HfcL1, Ha0L1.
            assert (HnanXL1 : fp_is_nan fmt_double (bv_unsigned XL1) = false) by (unfold XL1; rewrite unsigned_lit_small by exact HrngL1; exact HnanL1).
            rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ HnanXL1) in HfcL1.
            replace (reac_rate_snap_model XL1) with 44100 in Ha0L1 by (unfold XL1; vm_compute; reflexivity).
            lazymatch type of HSe1 with st_ok _ _ _ (restrict _ ?msc) =>
              pose proof (st_ok_restrict_mkst SEGS (w_H W) EC1 _ msc HSe1 eq_refl) as HshL1;
              rewrite HshL1 in HSe1; rewrite restrict_mkst_fx in HSe1;
              pose proof (fp_st_ok_fx SEGS _ fqL1 EC1 _ _ _ _ _ HSe1) as HSf1;
              rewrite <- restrict_mkst_fx in HSf1; clear HSe1 HshL1;
              jafter_call_keep_pi HSf1 34%nat regsL1 (mrestrict (w_H W) (ms_mem msc)) HPL1 [0; 1]%nat HSg1 end.
            match type of HSg1 with ?P -> _ =>
              assert (HQ : P); [ cbn [restrict ms_mem mkst]; repeat apply Forall_cons; try apply Forall_nil; apply mc_region_kept_refl
              | specialize (HSg1 HQ); clear HQ ] end.
            rewrite <- restrict_mkst_fx in HSg1. clear HSf1.
            lazymatch type of HSg1 with st_ok_pi _ _ ?Ex ?sx _ =>
              let s' := eval vm_compute in sx in change sx with s' in HSg1;
              set (EL1 := Ex) in HSg1 end.
            assert (HEIL1 : img_env VAL A_LIM EL1) by (unfold EL1; apply img_env_havoc; [exact HEIC1 | rewrite length_map; unfold A_TEXT, CLOB; cbn [length]; lia]).
            assert (EL1o : forall i, (i < 34)%nat -> ew EL1 i = ew EC1 i) by (intros ii Hi; unfold EL1; apply ew_havoc_old; exact Hi).
            assert (EL1h : forall i, (50 <= i)%nat -> ew EL1 i = ew EC1 i) by (intros ii Hi; unfold EL1; apply ew_havoc_above; cbn; lia).
            assert (UspL1 : bv_unsigned (ew EL1 2) = spZ regs) by (rewrite EL1o by lia; exact UspC1).
            pose proof (mc_shok_env EC1 EL1 _ (EL1o 32%nat ltac:(lia)) (EL1h (A_OBJ 65) ltac:(unfold A_OBJ; lia)) SHOK1) as SHOKL1.
            cbn [ms_mem mkst] in SHOKL1. clear SHOK1.
            pose proof (st_ok_pi_pin_reg' EL1 _ _ (10%bv : bv 5) 44100 HSg1 ltac:(cbn [restrict ms_regs mkst]; exact Ha0L1) eq_refl) as HSP1.
            clear HSg1.
            lazymatch type of HSP1 with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HSP1 end.
            pose proof (paj_run (fx := fqL1) B LAWS) as RUNd1.
            paj_run_tok RUNd1 HSP1 HJL1 SHOKL1 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspL1. }
            lazymatch type of HSP1 with st_ok_pi _ _ ?Ex _ _ => set (EC2 := Ex) in HSP1, SHOKL1 end.
            assert (EC2o : forall n, (n < 512)%nat -> ew EC2 n = ew EL1 n) by (intros n Hn; unfold EC2; rewrite ?ew_ewset_other by lia; reflexivity).
            assert (HEIC2 : img_env VAL A_LIM EC2) by (unfold EC2; repeat (apply img_env_ewset_hi; [|unfold A_LIM; lia]); exact HEIL1).
            assert (UspC2 : bv_unsigned (ew EC2 2) = spZ regs) by (rewrite EC2o by lia; exact UspL1).
            mc_chain_cur W EC2 regs mem UspC2 HKL1b HKL2a.
            mc_chainR_cur regs mem UspC2 HRL1b HRL2a.
            prreg HSP1 (Z_to_bv 5 10) R10L2.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              assert (Hu10L2 : bv_unsigned (getr (ms_regs msc) (Z_to_bv 5 10)) = 4000) by (rewrite R10L2; reflexivity);
              rewrite (st_ok_pi_restrict_mkst (w_H W) EC2 _ msc HSP1 eq_refl); cbn [ss_pc] end.
            destruct (reac_master_only_cadence_ns.cvt_ok 4000 ltac:(lia)) as (HflL2 & HrngL2 & HnanL2).
            set (XL2 := Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 4000))).
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
              assert (HstA2 : RiscvSemantics.step SEGS (@mkst fqL1 Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)) =
                MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 10) XL2 (@YK11.fp_regs fqL1)) (@YK11.fp_csr fqL1)) Rc (Z_to_bv 64 (BASE + 33316)) (mrestrict (w_H W) Mc) (seg_rom SEGS)));
              [ rewrite <- (mc_pc4 33312 33316 eq_refl ltac:(lia));
                rewrite (fp_step_fcvt_d_wu fqL1 SEGS Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)
                  (Z_to_bv 32 3524592979) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 3 0));
                [ rewrite Hu10L2, HflL2; change (fflags_bits no_flags) with 0; rewrite reac_master_only_cadence_ns.fcsr_keep; reflexivity
                | apply mc_fetch; vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv | vm_compute; reflexivity ]
              | ];
              eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with (f' := (mkFP (bvmap_set (Z_to_bv 5 10) XL2 (@YK11.fp_regs fqL1)) (@YK11.fp_csr fqL1))) (R' := Rc) (pc' := Z_to_bv 64 (BASE + 33316));
              [exact HstA2 | exact HJL1 | clear HJL1; intros mdA2 HJL1] end.
            pose proof HSP1 as HSc2. destruct HSc2 as (_ & _ & _ & _ & _ & _ & HRGc2 & _).
            cbn [abs_ss setpc ss_regs restrict ms_regs] in HRGc2.
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
            lazymatch type of HSP1 with
            | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
              pose proof (fp_switch SEGS fqL1 (mkFP (bvmap_set (Z_to_bv 5 10) XL2 (@YK11.fp_regs fqL1)) (@YK11.fp_csr fqL1)) EC2 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) Rc (Z_to_bv 64 (BASE + 33316)) HSP1 HRGc2) as HSd2
            end end.
            cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HSd2.
            rewrite (unsigned_lit_small (BASE + 33316)) in HSd2 by (pose proof pa_B_ok as HB; lia).
            lazymatch type of HSd2 with
            | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
              assert (HSe2 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 10) XL2 (@YK11.fp_regs fqL1)) (@YK11.fp_csr fqL1)) EC2 (mkSS 33316 sr rs rv G) msy) by exact HSd2
            end.
            clear HSd2 HSP1 HRGc2 HstA2 R10L2.
            pose proof (paj_run (fx := (mkFP (bvmap_set (Z_to_bv 5 10) XL2 (@YK11.fp_regs fqL1)) (@YK11.fp_csr fqL1))) B LAWS) as RUNc2.
            cbn [ms_mem mkst] in SHOKL1.
            paj_run_tok RUNc2 HSe2 HJL1 SHOKL1 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspC2. }
            mc_chain_cur W EC2 regs mem UspC2 HKL2a HKL2b.
            mc_chainR_cur regs mem UspC2 HRL2a HRL2b.
            prreg HSe2 (2%bv : bv 5) Q2L2. prreg HSe2 (3%bv : bv 5) Q3L2. prreg HSe2 (4%bv : bv 5) Q4L2. prreg HSe2 (1%bv : bv 5) Q1L2.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              eapply (mc_call_rate _ W EC2 _ msc _ _ (112 + ESTACK) (spZ regs) ly S W mem md (@nil (Z * Z)) lyL1 SL1 0 (-112) 33320 HSe2) end.
            { reflexivity. }
            { exact HJL1. }
            { unfold spZ at 1. rewrite Q2L2, UspC2. apply unsigned_lit_small. clear - Hceil Hslo Hshi H47 C1. unfold ESTACK in *. lia. }
            { reflexivity. }
            { lia. }
            { unfold ESTACK. lia. }
            { rewrite Q3L2, EC2o, EL1o, EC1o, E3 by lia. exact Hgp'. }
            { rewrite Q4L2, EC2o, EL1o, EC1o, E4 by lia. exact Htp'. }
            { exact Q1L2. }
            { lia. }
            { reflexivity. }
            { match goal with |- context [aview _ _ (ms_mem ?msc)] => apply (mc_keep_ro B W mem (ms_mem msc) (spZ regs + -112) (spZ regs)); [unfold ESTACK in *; lia | exact HKL2b | exact HRO] end. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL2b); [exact Hout97 | exact H6000]. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL2b); [exact Hout96 | exact H3837]. }
            intros fqL2 lyL2 SL2 regsL2 memL2 mdC2 HfrL2 HfcL2 HJL2 HPL2 Ha0L2 HpermL2 HmemL2. subst memL2.
            cbn [YK11.fp_regs YK11.fp_csr] in HfrL2, HfcL2, Ha0L2. rewrite fp_rg_same in HfcL2, Ha0L2.
            assert (HnanXL2 : fp_is_nan fmt_double (bv_unsigned XL2) = false) by (unfold XL2; rewrite unsigned_lit_small by exact HrngL2; exact HnanL2).
            rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ HnanXL2) in HfcL2.
            pose proof (mc_csr_trans _ _ _ HfcL1 HfcL2) as HfcL2'. clear HfcL2. rename HfcL2' into HfcL2.
            replace (reac_rate_snap_model XL2) with 48000 in Ha0L2 by (unfold XL2; vm_compute; reflexivity).
            lazymatch type of HSe2 with st_ok _ _ _ (restrict _ ?msc) =>
              pose proof (st_ok_restrict_mkst SEGS (w_H W) EC2 _ msc HSe2 eq_refl) as HshL2;
              rewrite HshL2 in HSe2; rewrite restrict_mkst_fx in HSe2;
              pose proof (fp_st_ok_fx SEGS _ fqL2 EC2 _ _ _ _ _ HSe2) as HSf2;
              rewrite <- restrict_mkst_fx in HSf2; clear HSe2 HshL2;
              jafter_call_keep_pi HSf2 50%nat regsL2 (mrestrict (w_H W) (ms_mem msc)) HPL2 [0; 1]%nat HSg2 end.
            match type of HSg2 with ?P -> _ =>
              assert (HQ : P); [ cbn [restrict ms_mem mkst]; repeat apply Forall_cons; try apply Forall_nil; apply mc_region_kept_refl
              | specialize (HSg2 HQ); clear HQ ] end.
            rewrite <- restrict_mkst_fx in HSg2. clear HSf2.
            lazymatch type of HSg2 with st_ok_pi _ _ ?Ex ?sx _ =>
              let s' := eval vm_compute in sx in change sx with s' in HSg2;
              set (EL2 := Ex) in HSg2 end.
            assert (HEIL2 : img_env VAL A_LIM EL2) by (unfold EL2; apply img_env_havoc; [exact HEIC2 | rewrite length_map; unfold A_TEXT, CLOB; cbn [length]; lia]).
            assert (EL2o : forall i, (i < 50)%nat -> ew EL2 i = ew EC2 i) by (intros ii Hi; unfold EL2; apply ew_havoc_old; exact Hi).
            assert (EL2h : forall i, (66 <= i)%nat -> ew EL2 i = ew EC2 i) by (intros ii Hi; unfold EL2; apply ew_havoc_above; cbn; lia).
            assert (UspL2 : bv_unsigned (ew EL2 2) = spZ regs) by (rewrite EL2o by lia; exact UspC2).
            pose proof (mc_shok_env EC2 EL2 _ (EL2o 32%nat ltac:(lia)) (EL2h (A_OBJ 65) ltac:(unfold A_OBJ; lia)) SHOKL1) as SHOKL2.
            cbn [ms_mem mkst] in SHOKL2. clear SHOKL1.
            pose proof (st_ok_pi_pin_reg' EL2 _ _ (10%bv : bv 5) 48000 HSg2 ltac:(cbn [restrict ms_regs mkst]; exact Ha0L2) eq_refl) as HSP2.
            clear HSg2.
            lazymatch type of HSP2 with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HSP2 end.
            pose proof (paj_run (fx := fqL2) B LAWS) as RUNd2.
            paj_run_tok RUNd2 HSP2 HJL2 SHOKL2 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspL2. }
            lazymatch type of HSP2 with st_ok_pi _ _ ?Ex _ _ => set (EC3 := Ex) in HSP2, SHOKL2 end.
            assert (EC3o : forall n, (n < 512)%nat -> ew EC3 n = ew EL2 n) by (intros n Hn; unfold EC3; rewrite ?ew_ewset_other by lia; reflexivity).
            assert (HEIC3 : img_env VAL A_LIM EC3) by (unfold EC3; repeat (apply img_env_ewset_hi; [|unfold A_LIM; lia]); exact HEIL2).
            assert (UspC3 : bv_unsigned (ew EC3 2) = spZ regs) by (rewrite EC3o by lia; exact UspL2).
            mc_chain_cur W EC3 regs mem UspC3 HKL2b HKL3a.
            mc_chainR_cur regs mem UspC3 HRL2b HRL3a.
            prreg HSP2 (Z_to_bv 5 10) R10L3.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              assert (Hu10L3 : bv_unsigned (getr (ms_regs msc) (Z_to_bv 5 10)) = 8000) by (rewrite R10L3; reflexivity);
              rewrite (st_ok_pi_restrict_mkst (w_H W) EC3 _ msc HSP2 eq_refl); cbn [ss_pc] end.
            destruct (reac_master_only_cadence_ns.cvt_ok 8000 ltac:(lia)) as (HflL3 & HrngL3 & HnanL3).
            set (XL3 := Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 8000))).
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
              assert (HstA3 : RiscvSemantics.step SEGS (@mkst fqL2 Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)) =
                MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 10) XL3 (@YK11.fp_regs fqL2)) (@YK11.fp_csr fqL2)) Rc (Z_to_bv 64 (BASE + 33316)) (mrestrict (w_H W) Mc) (seg_rom SEGS)));
              [ rewrite <- (mc_pc4 33312 33316 eq_refl ltac:(lia));
                rewrite (fp_step_fcvt_d_wu fqL2 SEGS Rc (Z_to_bv 64 (BASE + 33312)) (mrestrict (w_H W) Mc) (seg_rom SEGS)
                  (Z_to_bv 32 3524592979) (Z_to_bv 5 10) (Z_to_bv 5 10) (Z_to_bv 3 0));
                [ rewrite Hu10L3, HflL3; change (fflags_bits no_flags) with 0; rewrite reac_master_only_cadence_ns.fcsr_keep; reflexivity
                | apply mc_fetch; vm_compute; reflexivity | vm_compute; reflexivity | vm_refl_bv | vm_compute; reflexivity ]
              | ];
              eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with (f' := (mkFP (bvmap_set (Z_to_bv 5 10) XL3 (@YK11.fp_regs fqL2)) (@YK11.fp_csr fqL2))) (R' := Rc) (pc' := Z_to_bv 64 (BASE + 33316));
              [exact HstA3 | exact HJL2 | clear HJL2; intros mdA3 HJL2] end.
            pose proof HSP2 as HSc3. destruct HSc3 as (_ & _ & _ & _ & _ & _ & HRGc3 & _).
            cbn [abs_ss setpc ss_regs restrict ms_regs] in HRGc3.
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
            lazymatch type of HSP2 with
            | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
              pose proof (fp_switch SEGS fqL2 (mkFP (bvmap_set (Z_to_bv 5 10) XL3 (@YK11.fp_regs fqL2)) (@YK11.fp_csr fqL2)) EC3 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) Rc (Z_to_bv 64 (BASE + 33316)) HSP2 HRGc3) as HSd3
            end end.
            cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HSd3.
            rewrite (unsigned_lit_small (BASE + 33316)) in HSd3 by (pose proof pa_B_ok as HB; lia).
            lazymatch type of HSd3 with
            | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
              assert (HSe3 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 10) XL3 (@YK11.fp_regs fqL2)) (@YK11.fp_csr fqL2)) EC3 (mkSS 33316 sr rs rv G) msy) by exact HSd3
            end.
            clear HSd3 HSP2 HRGc3 HstA3 R10L3.
            pose proof (paj_run (fx := (mkFP (bvmap_set (Z_to_bv 5 10) XL3 (@YK11.fp_regs fqL2)) (@YK11.fp_csr fqL2))) B LAWS) as RUNc3.
            cbn [ms_mem mkst] in SHOKL2.
            paj_run_tok RUNc3 HSe3 HJL2 SHOKL2 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspC3. }
            mc_chain_cur W EC3 regs mem UspC3 HKL3a HKL3b.
            mc_chainR_cur regs mem UspC3 HRL3a HRL3b.
            prreg HSe3 (2%bv : bv 5) Q2L3. prreg HSe3 (3%bv : bv 5) Q3L3. prreg HSe3 (4%bv : bv 5) Q4L3. prreg HSe3 (1%bv : bv 5) Q1L3.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ =>
              eapply (mc_call_rate _ W EC3 _ msc _ _ (112 + ESTACK) (spZ regs) ly S W mem md (@nil (Z * Z)) lyL2 SL2 0 (-112) 33320 HSe3) end.
            { reflexivity. }
            { exact HJL2. }
            { unfold spZ at 1. rewrite Q2L3, UspC3. apply unsigned_lit_small. clear - Hceil Hslo Hshi H47 C1. unfold ESTACK in *. lia. }
            { reflexivity. }
            { lia. }
            { unfold ESTACK. lia. }
            { rewrite Q3L3, EC3o, EL2o, EC2o, EL1o, EC1o, E3 by lia. exact Hgp'. }
            { rewrite Q4L3, EC3o, EL2o, EC2o, EL1o, EC1o, E4 by lia. exact Htp'. }
            { exact Q1L3. }
            { lia. }
            { reflexivity. }
            { match goal with |- context [aview _ _ (ms_mem ?msc)] => apply (mc_keep_ro B W mem (ms_mem msc) (spZ regs + -112) (spZ regs)); [unfold ESTACK in *; lia | exact HKL3b | exact HRO] end. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL3b); [exact Hout97 | exact H6000]. }
            { apply (mc_keep_val _ _ _ _ _ _ _ HKL3b); [exact Hout96 | exact H3837]. }
            intros fqL3 lyL3 SL3 regsL3 memL3 mdC3 HfrL3 HfcL3 HJL3 HPL3 Ha0L3 HpermL3 HmemL3. subst memL3.
            cbn [YK11.fp_regs YK11.fp_csr] in HfrL3, HfcL3, Ha0L3. rewrite fp_rg_same in HfcL3, Ha0L3.
            assert (HnanXL3 : fp_is_nan fmt_double (bv_unsigned XL3) = false) by (unfold XL3; rewrite unsigned_lit_small by exact HrngL3; exact HnanL3).
            rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ HnanXL3) in HfcL3.
            pose proof (mc_csr_trans _ _ _ HfcL2 HfcL3) as HfcL3'. clear HfcL3. rename HfcL3' into HfcL3.
            replace (reac_rate_snap_model XL3) with 96000 in Ha0L3 by (unfold XL3; vm_compute; reflexivity).
            lazymatch type of HSe3 with st_ok _ _ _ (restrict _ ?msc) =>
              pose proof (st_ok_restrict_mkst SEGS (w_H W) EC3 _ msc HSe3 eq_refl) as HshL3;
              rewrite HshL3 in HSe3; rewrite restrict_mkst_fx in HSe3;
              pose proof (fp_st_ok_fx SEGS _ fqL3 EC3 _ _ _ _ _ HSe3) as HSf3;
              rewrite <- restrict_mkst_fx in HSf3; clear HSe3 HshL3;
              jafter_call_keep_pi HSf3 66%nat regsL3 (mrestrict (w_H W) (ms_mem msc)) HPL3 [0; 1]%nat HSg3 end.
            match type of HSg3 with ?P -> _ =>
              assert (HQ : P); [ cbn [restrict ms_mem mkst]; repeat apply Forall_cons; try apply Forall_nil; apply mc_region_kept_refl
              | specialize (HSg3 HQ); clear HQ ] end.
            rewrite <- restrict_mkst_fx in HSg3. clear HSf3.
            lazymatch type of HSg3 with st_ok_pi _ _ ?Ex ?sx _ =>
              let s' := eval vm_compute in sx in change sx with s' in HSg3;
              set (EL3 := Ex) in HSg3 end.
            assert (HEIL3 : img_env VAL A_LIM EL3) by (unfold EL3; apply img_env_havoc; [exact HEIC3 | rewrite length_map; unfold A_TEXT, CLOB; cbn [length]; lia]).
            assert (EL3o : forall i, (i < 66)%nat -> ew EL3 i = ew EC3 i) by (intros ii Hi; unfold EL3; apply ew_havoc_old; exact Hi).
            assert (EL3h : forall i, (82 <= i)%nat -> ew EL3 i = ew EC3 i) by (intros ii Hi; unfold EL3; apply ew_havoc_above; cbn; lia).
            assert (UspL3 : bv_unsigned (ew EL3 2) = spZ regs) by (rewrite EL3o by lia; exact UspC3).
            pose proof (mc_shok_env EC3 EL3 _ (EL3o 32%nat ltac:(lia)) (EL3h (A_OBJ 65) ltac:(unfold A_OBJ; lia)) SHOKL2) as SHOKL3.
            cbn [ms_mem mkst] in SHOKL3. clear SHOKL2.
            pose proof (st_ok_pi_pin_reg' EL3 _ _ (10%bv : bv 5) 96000 HSg3 ltac:(cbn [restrict ms_regs mkst]; exact Ha0L3) eq_refl) as HSP3.
            clear HSg3.
            lazymatch type of HSP3 with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HSP3 end.
            pose proof (paj_run (fx := fqL3) B LAWS) as RUNd3.
            paj_run_tok RUNd3 HSP3 HJL3 SHOKL3 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspL3. }
            lazymatch type of HSP3 with st_ok_pi _ _ ?Ex _ _ => set (EC4 := Ex) in HSP3, SHOKL3 end.
            assert (EC4o : forall n, (n < 512)%nat -> ew EC4 n = ew EL3 n) by (intros n Hn; unfold EC4; rewrite ?ew_ewset_other by lia; reflexivity).
            assert (HEIC4 : img_env VAL A_LIM EC4) by (unfold EC4; repeat (apply img_env_ewset_hi; [|unfold A_LIM; lia]); exact HEIL3).
            assert (UspC4 : bv_unsigned (ew EC4 2) = spZ regs) by (rewrite EC4o by lia; exact UspL3).
            mc_chain_cur W EC4 regs mem UspC4 HKL3b HKT1.
            mc_chainR_cur regs mem UspC4 HRL3b HRT1.
            match goal with |- SRr _ _ (mkCfg ?msc _) _ => rewrite (st_ok_pi_restrict_mkst (w_H W) EC4 _ msc HSP3 eq_refl); cbn [ss_pc] end.
            prreg HSP3 (Z_to_bv 5 2) R2T.
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
            assert (HrdnT : rdn SEGS (mrestrict (w_H W) Mc) (Z_to_bv 64 (spZ regs + -112)) 8 = Some (word_to_le_bytes 8 fv));
            [ lazymatch type of HSP3 with st_ok_pi _ _ _ ?sx (restrict _ ?msx) =>
                let r0 := eval vm_compute in (nth 1 (ss_mem sx) got_regionP) in
                pose proof (st_ok_region_nth EC4 (abs_ss VAL sx) (restrict (w_H W) msx) 1 r0 HSP3 eq_refl) as HregT end;
              cbn [restrict ms_mem] in HregT;
              rewrite <- UspC4; eapply (mc_fs0_rdn EC4 _ 2 _ _ _ _ _ _ (SOff 33 0) fv HregT eq_refl);
              [ cbn [In]; left; reflexivity
              | cbn [sv_denot]; rewrite EC4o, EL3o, EC3o, EL2o, EC2o, EL1o, EC1o, E33 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ]
            | ];
            assert (HstT : RiscvSemantics.step SEGS (@mkst fqL3 Rc (Z_to_bv 64 (BASE + 33488)) (mrestrict (w_H W) Mc) (seg_rom SEGS)) =
              MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3)) Rc (Z_to_bv 64 (BASE + 33492)) (mrestrict (w_H W) Mc) (seg_rom SEGS)));
            [ rewrite <- (mc_pc4 33488 33492 eq_refl ltac:(lia));
              rewrite (fp_step_fld fqL3 SEGS Rc (Z_to_bv 64 (BASE + 33488)) (mrestrict (w_H W) Mc) (seg_rom SEGS)
                (Z_to_bv 32 78855) (Z_to_bv 5 8) (Z_to_bv 5 2) (Z_to_bv 12 0) (Z_to_bv 64 (spZ regs + -112)) (word_to_le_bytes 8 fv));
              [ rewrite mc_word_rt; reflexivity
              | apply mc_fetch; vm_compute; reflexivity
              | vm_compute; reflexivity
              | vm_refl_bv
              | rewrite R2T, UspC4; replace (bv_signed (Z_to_bv 12 0)) with 0 by (vm_compute; reflexivity); unfold v_addi;
                rewrite unsigned_lit_small by (clear - Hceil Hslo Hshi H47 C1; unfold ESTACK in *; lia); f_equal; lia
              | exact HrdnT ]
            | ];
            eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with (f' := (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3))) (R' := Rc) (pc' := Z_to_bv 64 (BASE + 33492));
            [exact HstT | exact HJL3 | clear HJL3; intros mdT HJL3] end.
            pose proof HSP3 as HSPc. destruct HSPc as (_ & _ & _ & _ & _ & _ & HRGT & _).
            cbn [abs_ss setpc ss_regs restrict ms_regs] in HRGT.
            match goal with |- SRr _ _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
            lazymatch type of HSP3 with
            | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
              pose proof (fp_switch SEGS fqL3 (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3)) EC4 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) Rc (Z_to_bv 64 (BASE + 33492)) HSP3 HRGT) as HSQ0
            end end.
            cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HSQ0.
            rewrite (unsigned_lit_small (BASE + 33492)) in HSQ0 by (pose proof pa_B_ok as HB; lia).
            lazymatch type of HSQ0 with
            | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
              assert (HSQ : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3)) EC4 (mkSS 33492 sr rs rv G) msy) by exact HSQ0
            end.
            clear HSQ0 HSP3 HRGT HstT HrdnT R2T.
            pose proof (paj_run (fx := (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3))) B LAWS) as RUNT.
            paj_run_tok RUNT HSQ HJL3 SHOKL3 mc_Bspan.
            { awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact UspC4. }
            mc_chainR_cur regs mem UspC4 HRT1 HRT2.
            lazymatch type of HSQ with st_ok_pi _ _ ?Ex _ _ => set (EF := Ex) in HSQ end.
            assert (EFo : forall n, (n < 512)%nat -> ew EF n = ew EC4 n) by (intros n Hn; unfold EF; rewrite ?ew_ewset_other by lia; reflexivity).
            prreg HSQ (10%bv : bv 5) Q10T.
            prreg HSQ (1%bv : bv 5) Q1T.
            eapply (paj_ret_at (PL := PL_disco) W EF _ _ _ _ HSQ eq_refl ltac:(vm_compute; reflexivity)).
            intros matT.
            unfold treac_master_only_cadence_ns_post.
            exists (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fq)).
            cbn [YK11.fp_regs YK11.fp_csr].
            split; [apply mc_ke_fin; mc_ke_go|].
            split; [reflexivity|].
            unfold apost_base.
            exists (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fqL3)) (@YK11.fp_csr fqL3)).
            match goal with |- context [mkCfg (mkst (ms_regs ?msc) _ (ms_mem ?msc) _) _] => exists lyL3, SL3, (ms_regs msc), (ms_mem msc) end.
            eexists.
            split; [rewrite Q1T, EFo, EC4o, EL3o, EC3o, EL2o, EC2o, EL1o, EC1o, E1, Hra by lia; reflexivity|].
            split; [intros; reflexivity|]. split; [exact HfcL3|].
            split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJL3|].
            split; [eapply (aregs_preserved_of_st_ok SEGS _ EF _ _ regs _ HSQ); [split; [intros n Hn; rewrite EFo, EC4o, EL3o, EC3o, EL2o, EC2o, EL1o, EC1o by lia; apply (proj1 HAE); exact Hn | exact (proj2 HAE)] | vm_compute; reflexivity]|].
            split; [rewrite Q10T; reflexivity|].
            split; [eapply Permutation_trans; [exact HpermL3 | eapply Permutation_trans; [exact HpermL2 | exact HpermL1]]|].
            split; [reflexivity|].
            intros a Ha; apply HRT2; clear - Ha; unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK in Ha; unfold ESTACK in Ha; lia.

    *
      assert (Hfps1 : 1 <= fps < 2 ^ 31).
      { split; [|lia]. cbn [sv_denot] in Hc. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned in Hc.
        change (branch_taken BC_GE ?a ?b) with (negb (bv_lts a b)) in Hc.
        unfold bv_lts in Hc. rewrite Hsg in Hc.
        change (bv_signed (Z_to_bv 64 0)) with 0 in Hc.
        apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc. lia. }
      paj_run_tok RUN0 HS2 HJ1 SHOK1 mc_Bspan.
      -- awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
      -- mc_chain W E regs mem Usp HFr1 HK3 HK4.
         mc_chainR regs mem Usp HF1 HR3 HR4.
         prreg HS2 (Z_to_bv 5 10) R10.
         assert (Hu10 : bv_unsigned (getr (ms_regs ms2) (Z_to_bv 5 10)) = fps)
           by (rewrite R10, E10; apply unsigned_lit_small; lia).
         destruct (reac_master_only_cadence_ns.cvt_ok fps ltac:(lia)) as (Hfl & Hrng & Hnan).
         rewrite (st_ok_pi_restrict_mkst (w_H W) E _ _ HS2 eq_refl); cbn [ss_pc].
         assert (Hstep1 : RiscvSemantics.step SEGS (@mkst fq (ms_regs ms2) (Z_to_bv 64 (BASE + 33132)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS)) =
           MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq)) (@YK11.fp_csr fq))
              (ms_regs ms2) (Z_to_bv 64 (BASE + 33136)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS))).
         { rewrite <- (mc_pc4 33132 33136 eq_refl ltac:(lia)).
           rewrite (fp_step_fcvt_d_wu fq SEGS (ms_regs ms2) (Z_to_bv 64 (BASE + 33132)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS)
             (Z_to_bv 32 3524592723) (Z_to_bv 5 8) (Z_to_bv 5 10) (Z_to_bv 3 0)).
           - rewrite Hu10, Hfl. change (fflags_bits no_flags) with 0.
             rewrite reac_master_only_cadence_ns.fcsr_keep. reflexivity.
           - apply mc_fetch. vm_compute. reflexivity.
           - vm_compute. reflexivity.
           - vm_refl_bv.
           - vm_compute. reflexivity. }
         eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with
           (f' := mkFP (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq)) (@YK11.fp_csr fq))
           (R' := ms_regs ms2) (pc' := Z_to_bv 64 (BASE + 33136));
         [exact Hstep1 | exact HJ1 | clear HJ1; intros md3 HJ1].
         assert (Hstep2 : RiscvSemantics.step SEGS (@mkst (mkFP (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq)) (@YK11.fp_csr fq))
             (ms_regs ms2) (Z_to_bv 64 (BASE + 33136)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS)) =
           MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))
                 (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq))) (@YK11.fp_csr fq))
              (ms_regs ms2) (Z_to_bv 64 (BASE + 33140)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS))).
         { rewrite <- (mc_pc4 33136 33140 eq_refl ltac:(lia)).
           rewrite (fp_step_fmv_d _ SEGS (ms_regs ms2) (Z_to_bv 64 (BASE + 33136)) (mrestrict (w_H W) (ms_mem ms2)) (seg_rom SEGS)
             (Z_to_bv 32 579077459) (Z_to_bv 5 10) (Z_to_bv 5 8)).
           - cbn [YK11.fp_regs YK11.fp_csr]. rewrite fp_rg_same. reflexivity.
           - apply mc_fetch. vm_compute. reflexivity.
           - vm_compute. reflexivity.
           - vm_refl_bv. }
         eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with
           (f' := mkFP (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))
                 (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq))) (@YK11.fp_csr fq))
           (R' := ms_regs ms2) (pc' := Z_to_bv 64 (BASE + 33140));
         [exact Hstep2 | exact HJ1 | clear HJ1; intros md4 HJ1].
         pose proof HS2 as HS2c.
         destruct HS2c as (_ & _ & _ & _ & _ & _ & HRG2 & _).
         cbn [abs_ss setpc ss_regs restrict ms_regs] in HRG2.
         lazymatch type of HS2 with
         | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
           pose proof (fp_switch SEGS fq
             (mkFP (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))
                 (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq))) (@YK11.fp_csr fq))
             E (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) (ms_regs ms2) (Z_to_bv 64 (BASE + 33140)) HS2 HRG2) as HS3
         end.
         cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HS3.
         rewrite (unsigned_lit_small (BASE + 33140)) in HS3
           by (pose proof pa_B_ok as HB; lia).
         lazymatch type of HS3 with
         | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
           assert (HS4 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))
                 (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq))) (@YK11.fp_csr fq))
             E (mkSS 33140 sr rs rv G) msy) by exact HS3
         end.
         clear HS3 HS2 HRG2 Hstep1 Hstep2 R10.
         pose proof (paj_run (fx := mkFP (bvmap_set (Z_to_bv 5 10) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))
                 (bvmap_set (Z_to_bv 5 8) (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) (@YK11.fp_regs fq))) (@YK11.fp_csr fq)) B LAWS) as RUN2.
         cbn [ms_mem mkst] in SHOK1.
         paj_run_tok RUN2 HS4 HJ1 SHOK1 mc_Bspan.
         ++ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp.
         ++ mc_chain W E regs mem Usp HFr2 HK4 HK5.
            mc_chainR regs mem Usp HF2 HR4 HR5.
            prreg HS4 (2%bv : bv 5) Q2. prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4. prreg HS4 (1%bv : bv 5) Q1.
            eapply (mc_call_rate _ W E _ ms3 _ _ (112 + ESTACK) (spZ regs) ly S W mem md (@nil (Z * Z)) ly S 0 (-112) 33144 HS4).
            ** reflexivity.
            ** exact HJ1.
            ** unfold spZ at 1. rewrite Q2, Usp. apply unsigned_lit_small. clear - Hceil Hslo Hshi H47 C1. unfold ESTACK in *. lia.
            ** reflexivity.
            ** lia.
            ** unfold ESTACK. lia.
            ** rewrite Q3, E3. exact Hgp'.
            ** rewrite Q4, E4. exact Htp'.
            ** exact Q1.
            ** lia.
            ** reflexivity.
            ** apply (mc_keep_ro B W mem (ms_mem ms3) (spZ regs + -112) (spZ regs)); [unfold ESTACK in *; lia | exact HK5 | exact HRO].
            ** apply (mc_keep_val _ _ _ _ _ _ _ HK5); [exact Hout97 | exact H6000].
            ** apply (mc_keep_val _ _ _ _ _ _ _ HK5); [exact Hout96 | exact H3837].
            ** intros fq3 ly2 S2 regs2 mem2 md5 Hfr3 Hfc3 HJ2 HP2 Ha02 Hperm2 Hmem2. subst mem2.
               cbn [YK11.fp_regs YK11.fp_csr] in Hfr3, Hfc3, Ha02. rewrite fp_rg_same in Hfc3, Ha02.
               assert (HnanX : fp_is_nan fmt_double (bv_unsigned (Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps)))) = false)
                 by (rewrite unsigned_lit_small by exact Hrng; exact Hnan).
               rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ HnanX) in Hfc3.
               pose proof (st_ok_restrict_mkst SEGS (w_H W) E _ ms3 HS4 eq_refl) as Hsh3.
               rewrite Hsh3 in HS4. rewrite restrict_mkst_fx in HS4.
               pose proof (fp_st_ok_fx SEGS _ fq3 E _ _ _ _ _ HS4) as HS4f.
               rewrite <- restrict_mkst_fx in HS4f. clear HS4 Hsh3.
               jafter_call_keep_pi HS4f 34%nat regs2 (mrestrict (w_H W) (ms_mem ms3)) HP2 [0; 1; 2]%nat HS5.
               match type of HS5 with ?P -> _ =>
                 assert (HQ : P); [ cbn [restrict ms_mem mkst]; repeat apply Forall_cons; try apply Forall_nil; apply mc_region_kept_refl
                 | specialize (HS5 HQ); clear HQ ] end.
               rewrite <- restrict_mkst_fx in HS5. clear HS4f.
               lazymatch type of HS5 with st_ok_pi _ _ ?Ex ?sx _ =>
                 let s' := eval vm_compute in sx in change sx with s' in HS5;
                 set (E5 := Ex) in HS5 end.
               assert (HEI5 : img_env VAL A_LIM E5) by (unfold E5; apply img_env_havoc; [exact HEI | rewrite length_map; unfold A_TEXT, CLOB; cbn [length]; lia]).
               assert (E5o : forall i, (i < 34)%nat -> ew E5 i = ew E i) by (intros i Hi; unfold E5; apply ew_havoc_old; exact Hi).
               assert (E5h : forall i, (50 <= i)%nat -> ew E5 i = ew E i) by (intros i Hi; unfold E5; apply ew_havoc_above; cbn; lia).
               assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite E5o by lia; exact Usp).
               pose proof (mc_shok_env E E5 _ (E5o 32%nat ltac:(lia)) (E5h (A_OBJ 65) ltac:(unfold A_OBJ; lia)) SHOK1) as SHOK5.
               cbn [ms_mem mkst] in SHOK5.
               pose proof (paj_run (fx := fq3) B LAWS) as RUN3.
               paj_run_tok RUN3 HS5 HJ2 SHOK5 mc_Bspan.
               --- awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp5.
               --- mc_chain W E5 regs mem Usp5 HFr3 HK5 HK6.
                   mc_chainR regs mem Usp5 HF3 HR5 HR6.
                   rewrite (st_ok_pi_restrict_mkst (w_H W) E5 _ ms4 HS5 eq_refl); cbn [ss_pc].
                   set (X := Z_to_bv 64 (fst (fp_of_int fmt_double RNE false 32 fps))) in *.
                   assert (Hf8 : Sem.reg_get (@YK11.fp_regs fq3) (Z_to_bv 5 8) = X).
                   { rewrite (Hfr3 (Z_to_bv 5 8) ltac:(vm_compute; discriminate)). rewrite !fp_rg_other by (vm_compute; discriminate). apply fp_rg_same. }
                   assert (Hstep3 : RiscvSemantics.step SEGS (@mkst fq3 (ms_regs ms4) (Z_to_bv 64 (BASE + 33148)) (mrestrict (w_H W) (ms_mem ms4)) (seg_rom SEGS)) =
                     MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 10) X (@YK11.fp_regs fq3)) (@YK11.fp_csr fq3)) (ms_regs ms4) (Z_to_bv 64 (BASE + 33152)) (mrestrict (w_H W) (ms_mem ms4)) (seg_rom SEGS))).
                   { rewrite <- (mc_pc4 33148 33152 eq_refl ltac:(lia)).
                     rewrite (fp_step_fmv_d fq3 SEGS (ms_regs ms4) (Z_to_bv 64 (BASE + 33148)) (mrestrict (w_H W) (ms_mem ms4)) (seg_rom SEGS) (Z_to_bv 32 579077459) (Z_to_bv 5 10) (Z_to_bv 5 8)).
                     - rewrite Hf8. reflexivity.
                     - apply mc_fetch. vm_compute. reflexivity.
                     - vm_compute. reflexivity.
                     - vm_refl_bv. }
                   eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with
                     (f' := mkFP (bvmap_set (Z_to_bv 5 10) X (@YK11.fp_regs fq3)) (@YK11.fp_csr fq3))
                     (R' := ms_regs ms4) (pc' := Z_to_bv 64 (BASE + 33152));
                   [exact Hstep3 | exact HJ2 | clear HJ2; intros md6 HJ2].
                   pose proof HS5 as HS5c. destruct HS5c as (_ & _ & _ & _ & _ & _ & HRG5 & _).
                   cbn [abs_ss setpc ss_regs restrict ms_regs] in HRG5.
                   lazymatch type of HS5 with
                   | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
                     pose proof (fp_switch SEGS fq3 (mkFP (bvmap_set (Z_to_bv 5 10) X (@YK11.fp_regs fq3)) (@YK11.fp_csr fq3))
                       E5 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) (ms_regs ms4) (Z_to_bv 64 (BASE + 33152)) HS5 HRG5) as HS6
                   end.
                   cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HS6.
                   rewrite (unsigned_lit_small (BASE + 33152)) in HS6 by (pose proof pa_B_ok as HB; lia).
                   lazymatch type of HS6 with
                   | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
                     assert (HS7 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 10) X (@YK11.fp_regs fq3)) (@YK11.fp_csr fq3))
                       E5 (mkSS 33152 sr rs rv G) msy) by exact HS6
                   end.
                   clear HS6 HS5 HRG5 Hstep3.
                   pose proof (paj_run (fx := mkFP (bvmap_set (Z_to_bv 5 10) X (@YK11.fp_regs fq3)) (@YK11.fp_csr fq3)) B LAWS) as RUN4.
                   cbn [ms_mem mkst] in SHOK5.
                   paj_run_tok RUN4 HS7 HJ2 SHOK5 mc_Bspan.
                   +++ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp5.
                   +++ mc_chain W E5 regs mem Usp5 HFr4 HK6 HK7.
                       mc_chainR regs mem Usp5 HF4 HR6 HR7.
                       prreg HS7 (2%bv : bv 5) Q2b. prreg HS7 (3%bv : bv 5) Q3b. prreg HS7 (4%bv : bv 5) Q4b. prreg HS7 (1%bv : bv 5) Q1b.
                       eapply (mc_call_rate _ W E5 _ ms5 _ _ (112 + ESTACK) (spZ regs) ly S W mem md (@nil (Z * Z)) ly2 S2 0 (-112) 33156 HS7).
                       *** reflexivity.
                       *** exact HJ2.
                       *** unfold spZ at 1. rewrite Q2b, Usp5. apply unsigned_lit_small. clear - Hceil Hslo Hshi H47 C1. unfold ESTACK in *. lia.
                       *** reflexivity.
                       *** lia.
                       *** unfold ESTACK. lia.
                       *** rewrite Q3b, E5o, E3 by lia. exact Hgp'.
                       *** rewrite Q4b, E5o, E4 by lia. exact Htp'.
                       *** exact Q1b.
                       *** lia.
                       *** reflexivity.
                       *** apply (mc_keep_ro B W mem (ms_mem ms5) (spZ regs + -112) (spZ regs)); [unfold ESTACK in *; lia | exact HK7 | exact HRO].
                       *** apply (mc_keep_val _ _ _ _ _ _ _ HK7); [exact Hout97 | exact H6000].
                       *** apply (mc_keep_val _ _ _ _ _ _ _ HK7); [exact Hout96 | exact H3837].
                       *** intros fq5 ly3 S3 regs3 mem3 md7 Hfr5 Hfc5 HJ3 HP3 Ha03 Hperm3 Hmem3. subst mem3.
                           cbn [YK11.fp_regs YK11.fp_csr] in Hfr5, Hfc5, Ha03. rewrite fp_rg_same in Hfc5, Ha03.
                           rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ HnanX) in Hfc5.
                           pose proof (mc_csr_trans _ _ _ Hfc3 Hfc5) as Hfc5'. clear Hfc5. rename Hfc5' into Hfc5.
                           pose proof (st_ok_restrict_mkst SEGS (w_H W) E5 _ ms5 HS7 eq_refl) as Hsh5.
                           rewrite Hsh5 in HS7. rewrite restrict_mkst_fx in HS7.
                           pose proof (fp_st_ok_fx SEGS _ fq5 E5 _ _ _ _ _ HS7) as HS7f.
                           rewrite <- restrict_mkst_fx in HS7f. clear HS7 Hsh5.
                           jafter_call_keep_pi HS7f 50%nat regs3 (mrestrict (w_H W) (ms_mem ms5)) HP3 [0; 1; 2]%nat HS8.
                           match type of HS8 with ?P -> _ =>
                             assert (HQ : P); [ cbn [restrict ms_mem mkst]; repeat apply Forall_cons; try apply Forall_nil; apply mc_region_kept_refl
                             | specialize (HS8 HQ); clear HQ ] end.
                           rewrite <- restrict_mkst_fx in HS8. clear HS7f.
                           lazymatch type of HS8 with st_ok_pi _ _ ?Ex ?sx _ =>
                             let s' := eval vm_compute in sx in change sx with s' in HS8;
                             set (E6 := Ex) in HS8 end.
                           assert (HIE6 : img_env VAL A_LIM E6) by (unfold E6; apply img_env_havoc; [exact HEI5 | rewrite length_map; unfold A_TEXT, CLOB; cbn [length]; lia]).
                           assert (E6o : forall i, (i < 50)%nat -> ew E6 i = ew E5 i) by (intros i Hi; unfold E6; apply ew_havoc_old; exact Hi).
                           assert (E6h : forall i, (66 <= i)%nat -> ew E6 i = ew E5 i) by (intros i Hi; unfold E6; apply ew_havoc_above; cbn; lia).
                           assert (Usp6 : bv_unsigned (ew E6 2) = spZ regs) by (rewrite E6o by lia; exact Usp5).
                           pose proof (mc_shok_env E5 E6 _ (E6o 32%nat ltac:(lia)) (E6h (A_OBJ 65) ltac:(unfold A_OBJ; lia)) SHOK5) as SHOK6.
                           cbn [ms_mem mkst] in SHOK6.
                           assert (E5_38 : ew E5 38 = getr regs2 10).
                           { unfold E5. exact (ew_havoc_new E 34 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0) ltac:(rewrite length_map; unfold CLOB; cbn [length]; lia)). }
                           prreg HS8 (8%bv : bv 5) R8c.
                           assert (Hs0v : getr regs3 8 = getr regs2 10) by (rewrite R8c, E6o, E5_38 by lia; reflexivity).
                           rewrite Ha02 in Hs0v. clear R8c.
                           pose proof (paj_run (fx := fq5) B LAWS) as RUN5.
                           destruct (reac_master_only_cadence_ns.snap_cases X) as [HM|[HM|HM]]; rewrite HM in Hs0v, Ha03;
                           (lazymatch type of Ha03 with getr _ _ = w64 ?z =>
                              pose proof (st_ok_pi_pin_reg' E6 _ _ (10%bv : bv 5) z HS8 ltac:(cbn [restrict ms_regs mkst]; exact Ha03) eq_refl) as HS9 end);
                           clear HS8;
                           (lazymatch type of Hs0v with getr _ _ = w64 ?z =>
                              pose proof (st_ok_pi_pin_reg' E6 _ _ (8%bv : bv 5) z HS9 ltac:(cbn [restrict ms_regs mkst]; exact Hs0v) eq_refl) as HS10 end);
                           clear HS9;
                           (lazymatch type of HS10 with st_ok_pi _ _ _ ?sx _ => let s' := eval vm_compute in sx in change sx with s' in HS10 end);
                           (paj_run_tok RUN5 HS10 HJ3 SHOK6 mc_Bspan;
                            [ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp6
                            |  ]).
                           all: mc_chain W E6 regs mem Usp6 HFr5 HK7 HK8.
                           all: mc_chainR regs mem Usp6 HF5 HR7 HR8.
                           all: rewrite (st_ok_pi_restrict_mkst (w_H W) E6 _ ms6 HS10 eq_refl); cbn [ss_pc].
                           all: prreg HS10 (Z_to_bv 5 2) R2e.
                           all: assert (Hrdn : rdn SEGS (mrestrict (w_H W) (ms_mem ms6)) (Z_to_bv 64 (spZ regs + -112)) 8 = Some (word_to_le_bytes 8 fv));
                             [ lazymatch type of HS10 with st_ok_pi _ _ _ ?sx (restrict _ ?msx) =>
                                 let r0 := eval vm_compute in (nth 0 (ss_mem sx) got_regionP) in
                                 pose proof (st_ok_region_nth E6 (abs_ss VAL sx) (restrict (w_H W) msx) 0 r0 HS10 eq_refl) as Hreg end;
                               cbn [restrict ms_mem] in Hreg;
                               rewrite <- Usp6; eapply (mc_fs0_rdn E6 _ 2 _ _ _ _ _ _ (SOff 33 0) fv Hreg eq_refl);
                               [ cbn [In]; left; reflexivity
                               | cbn [sv_denot]; rewrite E6o, E5o, E33 by lia; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ]
                             | ].
                           all: assert (Hstep5 : RiscvSemantics.step SEGS (@mkst fq5 (ms_regs ms6) (Z_to_bv 64 (BASE + 33488)) (mrestrict (w_H W) (ms_mem ms6)) (seg_rom SEGS)) =
                               MachineOk (@mkst (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5)) (ms_regs ms6) (Z_to_bv 64 (BASE + 33492)) (mrestrict (w_H W) (ms_mem ms6)) (seg_rom SEGS)));
                             [ rewrite <- (mc_pc4 33488 33492 eq_refl ltac:(lia));
                               rewrite (fp_step_fld fq5 SEGS (ms_regs ms6) (Z_to_bv 64 (BASE + 33488)) (mrestrict (w_H W) (ms_mem ms6)) (seg_rom SEGS)
                                 (Z_to_bv 32 78855) (Z_to_bv 5 8) (Z_to_bv 5 2) (Z_to_bv 12 0) (Z_to_bv 64 (spZ regs + -112)) (word_to_le_bytes 8 fv));
                               [ rewrite mc_word_rt; reflexivity
                               | apply mc_fetch; vm_compute; reflexivity
                               | vm_compute; reflexivity
                               | vm_refl_bv
                               | rewrite R2e, Usp6; replace (bv_signed (Z_to_bv 12 0)) with 0 by (vm_compute; reflexivity); unfold v_addi;
                                 rewrite unsigned_lit_small by (clear - Hceil Hslo Hshi H47 C1; unfold ESTACK in *; lia); f_equal; lia
                               | exact Hrdn ]
                             | ].
                           all: eapply (fp_keep_step SEGS B LAWS pa_wx pa_segs_low W) with
                               (f' := mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5))
                               (R' := ms_regs ms6) (pc' := Z_to_bv 64 (BASE + 33492));
                             [exact Hstep5 | exact HJ3 | clear HJ3; intros md8 HJ3].
                           all: pose proof HS10 as HS10c; destruct HS10c as (_ & _ & _ & _ & _ & _ & HRG10 & _);
                             cbn [abs_ss setpc ss_regs restrict ms_regs] in HRG10.
                           all: lazymatch type of HS10 with
                             | st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
                               pose proof (fp_switch SEGS fq5 (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5))
                                 E6 (abs_ss VAL ssx) msx (w_H W) (ss_regs ssx) (ms_regs ms6) (Z_to_bv 64 (BASE + 33492)) HS10 HRG10) as HS11
                             end.
                           all: cbn [abs_ss setpc ss_regs ss_fregs ss_mem ss_facts] in HS11.
                           all: rewrite (unsigned_lit_small (BASE + 33492)) in HS11 by (pose proof pa_B_ok as HB; lia).
                           all: lazymatch type of HS11 with
                             | st_ok _ _ (mkSST _ ?sr ?fr ?rs ?rv ?G) ?msy =>
                               assert (HS12 : @st_ok_pi SEGS VAL (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5))
                                 E6 (mkSS 33492 sr rs rv G) msy) by exact HS11
                             end.
                           all: clear HS11 HS10 HRG10 Hstep5 Hrdn R2e.
                           all: pose proof (paj_run (fx := mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5)) B LAWS) as RUN6.
                           all: (paj_run_tok RUN6 HS12 HJ3 SHOK6 mc_Bspan;
                             [ awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact Usp6
                             |  ]).
                           all: mc_chainR regs mem Usp6 HF6 HR8 HR9.
                           all: prreg HS12 (10%bv : bv 5) Q10f.
                           all: prreg HS12 (1%bv : bv 5) Q1f.
                           all: eapply (paj_ret_at (PL := PL_disco) W E6 _ _ _ _ HS12 eq_refl ltac:(vm_compute; reflexivity)).
                           all: intros matF.
                           all: unfold treac_master_only_cadence_ns_post.
                           all: exists (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq)).
                           all: cbn [YK11.fp_regs YK11.fp_csr].
                           all: split; [apply mc_ke_fin; mc_ke_go|].
                           all: split; [reflexivity|].
                           all: unfold apost_base.
                           all: exists (mkFP (bvmap_set (Z_to_bv 5 8) fv (@YK11.fp_regs fq5)) (@YK11.fp_csr fq5)).
                           all: exists ly3, S3, (ms_regs ms7), (ms_mem ms7).
                           all: eexists.
                           all: split; [rewrite Q1f, E6o, E5o, E1, Hra by lia; reflexivity|].
                           all: split; [intros; reflexivity|]. all: split; [exact Hfc5|].
                           all: split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3|].
                           all: split; [eapply (aregs_preserved_of_st_ok SEGS _ E6 _ _ regs _ HS12); [unfold E6, E5; env_agree_chain HAE | vm_compute; reflexivity]|].
                           all: split; [rewrite Q10f; reflexivity|].
                           all: split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm2]|].
                           all: split; [reflexivity|].
                           all: intros a Ha; apply HR9; clear - Ha; unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK in Ha; unfold ESTACK in Ha; lia.
Qed.
End h.
End f.
End d.
