(* G4: expected's return at EX_R 0x81704 (restore ra, s0..s11 from the frame; sp += 208; ret): ex_seg_R. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YFen.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI16 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v ACeg.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn FMW_lib FMW_ex_base.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* frame slots as a symbolic region: chunk (offset, j) holds extra atom 32 + j (after G3's rd_slot_chunks) *)
Definition ex_slot_chunks (cs : list (Z * nat)) : list YP09.chunk :=
  map (fun c => YP09.mkChunk (fst c) (CVal 8 (SOff (32 + snd c) 0))) cs.

Section f. Context {fx : YK11.FPState}.
Lemma ex_chunks_ok : forall E m b cs,
  Forall (fun c => val_mem tfibsegs m (b + fst c) 8 (bv_unsigned (ew E (32 + snd c)))) cs ->
  Forall (YP09.chunk_ok tfibsegs E m b) (ex_slot_chunks cs).
Proof.
  intros E m b cs H. induction H as [|c cs Hc _ IH]; [constructor|]. constructor; [|exact IH].
  apply (chunk_ok_val tfibsegs E m b (fst c) 8 (SOff (32 + snd c) 0) (bv_unsigned (ew E (32 + snd c)))).
  - cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
  - pose proof (bv_unsigned_in_range _ (ew E (32 + snd c))) as R. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R.
    exact R.
  - cbn. lia.
  - exact Hc.
Qed.
End f.

(* the saved registers as chunks: EX_SAVED's j-th slot holds atom 32 + j *)
Definition EX_SAVED_CH : list (Z * nat) :=
  [(200, 0%nat); (192, 1%nat); (184, 2%nat); (176, 3%nat); (168, 4%nat); (160, 5%nat); (152, 6%nat); (144, 7%nat);
   (136, 8%nat); (128, 9%nat); (120, 10%nat); (112, 11%nat); (104, 12%nat)].
Definition ex_frameR : YP09.region := YP09.mkRegion (Some 2%nat) 0 208 0 0 (ex_slot_chunks EX_SAVED_CH).
Definition ss_R : sstate :=
  mkSS EX_R sr_atoms [ex_frameR] None (mkFacts [(2%nat, mkAF (2^46) (2^47) 4)] [] []).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Definition ex_savedv (regs : bvmap 5 word) : list word :=
  map (fun s => getr regs (Z_to_bv 5 (snd s))) EX_SAVED.

Lemma ex_R_entry : forall cx ly3 S3 W3 regs3 mem3 md3,
  ex_base B cx -> ex_com B cx ly3 S3 W3 regs3 mem3 md3 ->
  st_ok tfibsegs (Ereg regs3 (ex_savedv (cx_regs cx))) ss_R
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 EX_R) mem3 (seg_rom tfibsegs))).
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 HB HC.
  destruct HB as ((HPRE & _) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  rewrite restrict_mkst_fx.
  set (E := Ereg regs3 (ex_savedv (cx_regs cx))).
  assert (Usp : bv_unsigned (ew E 2) = cx_F cx).
  { subst E. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), Rsp. apply unsigned_lit_small.
    unfold cx_F, cx_sp. lia. }
  unfold ss_R. apply (entry_st_ok_full tfibsegs); change (Ereg regs3 (ex_savedv (cx_regs cx))) with E.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ex_frameR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    unfold cx_F, cx_sp in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply ex_chunks_ok. unfold ex_saved_ok, EX_SAVED in HSV. unfold EX_SAVED_CH.
    repeat (apply Forall_cons; [|]); try apply Forall_nil;
      repeat match goal with H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end;
      cbn [fst snd] in *;
      lazymatch goal with |- val_mem _ _ _ _ (bv_unsigned (ew E ?n)) =>
        let j := eval vm_compute in (n - 32)%nat in
        replace (ew E n) with (nth j (ex_savedv (cx_regs cx)) (Z_to_bv 64 0))
          by (subst E; symmetry; exact (ew_Ereg_extra regs3 _ j)) end;
      cbn [nth ex_savedv map EX_SAVED snd]; assumption.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp. change (2 ^ 4) with 16. split; [|exact I].
    unfold cx_F, cx_sp in *. split; [lia|].
    replace (spZ (cx_regs cx) - 208) with (spZ (cx_regs cx) + (-13) * 16) by lia. rewrite Z_mod_plus_full.
    split; [exact Hal16 | lia].
Qed.
Theorem ex_seg_R_holds : ex_seg_R B.
Proof.
  intros cx ly3 S3 W3 regs3 mem3 md3 HB HC R10.
  pose proof LAWS as HL. pose proof fmw_segs_low as Hsegs. pose proof fmw_wx as Hwx.
  pose proof HB as ((HPRE & HRO) & _).
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ex_R_entry cx ly3 S3 W3 regs3 mem3 md3 HB HC) as HS.
  destruct HC as (HJ & Hbl & HGL & Rsp & Rgp & Rtp & R25 & HSV & _).
  assert (HSTK : STK_expected = 208 + 8224) by reflexivity.
  set (E := Ereg regs3 (ex_savedv (cx_regs cx))) in *.
  assert (EE : forall n (q : bv 5), Z.of_nat n = bv_unsigned q -> ew E n = getr regs3 q)
    by (intros n q Hn; subst E; apply ew_Ereg_nat; exact Hn).
  assert (EX : forall j, ew E (32 + j) = nth j (ex_savedv (cx_regs cx)) (Z_to_bv 64 0))
    by (intros j; subst E; apply ew_Ereg_extra).
  assert (SHOK : sh_ok tfibsegs EX_Bx [] E
    (mrestrict (w_H W3) (ms_mem (mkst regs3 (Z_to_bv 64 EX_R) mem3 (seg_rom tfibsegs))))) by constructor.
  change mem3 with (ms_mem (mkst regs3 (Z_to_bv 64 EX_R) mem3 (seg_rom tfibsegs))) in HJ.
  unfold cfg_at. change (w64 EX_R) with (Z_to_bv 64 EX_R).
  aj_run_tok EX_tbl_ok HS HJ SHOK EX_Bspan.
  { awr_ok_tac. }
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) (ms_mem ms) a = aview tfibsegs (w_H W3) mem3 a).
  { intros a Ha. apply (fw_nowin tfibsegs _ _ _ _ _ HFr); [vm_compute; reflexivity | exact Ha]. }
  assert (KL : fw_low tfibsegs (w_H W3) mem3 (ms_mem ms)) by (intros a Ha; apply AV; lia).
  eapply (SRr_ret_at tfibsegs EX_tbl EX_tbl_ok Hwx W3); [exact HS | reflexivity | vm_compute; reflexivity |].
  intros mat'. unfold ex_post, fpost, apost_base.
  exists ly3, S3, (ms_regs ms), (ms_mem ms). eexists.
  split.
  { assert (RA : getr (ms_regs ms) 1 = getr (cx_regs cx) 1).
    { lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msx) =>
        rewrite (st_ok_restrict_reg tfibsegs _ E ss msx (1%bv : bv 5) HS);
        let e := eval vm_compute in (sr_get (ss_regs ss) (1%bv : bv 5)) in
        change (sr_get (ss_regs ss) (1%bv : bv 5)) with e end.
      cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EX 0%nat). }
    rewrite RA, Hra. reflexivity. }
  split; [apply (ajournal_materialize tfibsegs B HL Hsegs); exact HJ|].
  split.
  { intros q Hq. unfold acallee_saved in Hq.
    assert (Hq' : q = 2 \/ q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22 \/
      q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27) by lia.
    repeat (destruct Hq' as [->|Hq']); try subst q;
      lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msx) =>
        lazymatch goal with |- getr _ ?r = _ =>
          rewrite (st_ok_restrict_reg tfibsegs _ E ss msx r HS);
          let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end end;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      first [ rewrite (EE 2%nat 2%bv eq_refl), Rsp, unsigned_lit_small by (unfold cx_F, cx_sp; lia);
              unfold cx_F, cx_sp, spZ; rewrite Z.sub_add, Z_to_bv_bv_unsigned; reflexivity
            | rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl); exact Rgp
            | rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl); exact Rtp
            | lazymatch goal with |- ew E ?n = _ =>
                let j := eval vm_compute in (n - 32)%nat in
                change n with (32 + j)%nat; rewrite (EX j); reflexivity end
            ]. }
  split.
  { lazymatch type of HS with st_ok _ _ ?ss (restrict _ ?msx) =>
      rewrite (st_ok_restrict_reg tfibsegs _ E ss msx (10%bv : bv 5) HS);
      let e := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in change (sr_get (ss_regs ss) (10%bv : bv 5)) with e end.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 10%nat 10%bv eq_refl). exact R10. }
  split; [exact Hbl|].
  exact (fw_glob_low tfibsegs W3 mem3 _ _ _ _ _ KL HGL).
Qed.
End W.

Print Assumptions ex_seg_R_holds.
