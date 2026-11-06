(* fuzz_preset, image A' (the #102 asan image, pinned 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the
   journal-generic pieces of the walk of check_reject_clean (Wcrc102.v). A PORT of h-hpreset-7's S911Kit.v
   (origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2, lib/A/Prog/S911Kit.v), cut down to check_reject_clean:
   (1) the body read from the image's segments (YP02.build_table over AB1v's tfibsegs at the generated entry and
       length of Crc102Syms.v, so a different body fails the build);
   (2) the image facts the walk takes, as one record c102_img over the listing class (generic over {L} {PA}); the
       instance file Crc102InstA.v proves it at PI_prog_A by computation;
   (3) the entry state and the frame lemma (S911Kit.v's, unchanged: they read YCbqG's afn_pre_x only), and the ledger
       keep RESTATED for the #102 kit's prh_ledger (lib/A/PRH_Base.v blob 3004a98fe2d9: thirteen arguments, the cells
       g_most / g_own_ran_out added), read through its named projections;
   (4) the run / branch tactics. c102_run is S911Kit.v's s911_run plus the MEMNORM KEEP the m-form posts ask
       (PRH_Base.v fpostm, fQmn): before each run it builds, from the run's start state, the implication
       `memnorm mem0 -> memnorm m'` for every m' framed by the run (YGcallMxmn.v memnorm_frame_of), and after the
       run it applies it to the run's own frame_of fact.
   Numerals: 16 (LENGTH: frame), 2 ^ 46 / 2 ^ 47 / 4 (DERIVED: the stack atom's range and alignment, astk_ok), 8
   (LENGTH: word); every ADDRESS is Crc102Syms.v's (generated) or the PrhImg instance's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crc102Syms.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- (1) the body, read from the image ---- *)
Definition tbl_crc102 : ctable := Eval vm_compute in
  build_table tfibsegs A102_check_reject_clean N102_check_reject_clean TEmpty.
Lemma tbl_crc102_img : table_ok tfibsegs tbl_crc102.
Proof.
assert (E : tbl_crc102 = build_table tfibsegs A102_check_reject_clean N102_check_reject_clean TEmpty)
  by (vm_cast_no_check (eq_refl tbl_crc102)).
rewrite E. apply build_table_ok0. unfold A102_check_reject_clean. lia.
Qed.

(* ---- (2) the image facts the walk takes, per instance PA of the listing class: the body is the image's, the three
   entries are the listing's, and `static const struct pj empty` is 56 read-only zero image bytes ---- *)
Record c102_img {rc : YM05.RunCeil} {L : ptable asym} (PA : PAImg L) : Prop := {
  ci_crc : table_ok pa_segs tbl_crc102;
  ci_e_crc : pa_sigma AS_check_reject_clean = A102_check_reject_clean;
  ci_e_live : pa_sigma AS_fuzz_alloc_live = A102_fuzz_alloc_live;
  ci_e_bcmp : pa_sigma AS___wrap_bcmp = A102_wrap_bcmp;
  ci_empty : forall i, 0 <= i < 56 ->
    in_roP pa_segs pa_relro_lo pa_relro_hi (A102_crc_empty + i) /\
    seg_rom pa_segs (Z_to_bv 64 (A102_crc_empty + i)) = Some (Z_to_bv 8 0)
}.

(* ---- (3) the entry state of a function whose prologue is `addi sp, sp, -f` (S911Kit.v :73-118, unchanged) ---- *)
Definition c102_fstk (f : Z) : YP09.region := YP09.mkRegion (Some 2%nat) (- f) 0 (- f) 0 [].
Definition c102_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition c102_ss0 (pc f : Z) : sstate := mkSS pc sr_atoms [c102_fstk f] None c102_facts.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma c102_sp : forall segs B ARx STK ly S Hp (W : world segs) regs mem md ch,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch ->
  spZ regs mod 16 = 0 /\ YM05.alloc_ceiling + STK <= spZ regs /\ spZ regs <= 2 ^ 47 /\ 0 <= STK.
Proof.
intros segs B ARx STK ly S Hp W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop). lia.
Qed.
Lemma c102_entry : forall segs B ARx STK f ly S Hp (W : world segs) regs mem md ch pc,
  afn_pre_x segs B ARx STK ly S Hp W regs mem md ch -> 0 <= f <= STK -> regions_wf [c102_fstk f] = true ->
  st_ok segs (Ereg regs []) (c102_ss0 pc f) (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs))).
Proof.
intros segs B ARx STK f ly S Hp W regs mem md ch pc HPRE Hf Hwf.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (c102_sp segs B ARx STK ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
rewrite restrict_mkst_fx.
assert (E2 : bv_unsigned (ew (Ereg regs []) 2) = spZ regs) by (rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
unfold c102_ss0. apply (entry_st_ok_full segs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor].
  apply (region_ok_stack segs _ _ 2 (spZ regs) (- f) E2); [lia | lia |].
  intros a Ha. apply (apresent_writable segs). apply Hpres. lia.
- cbn. tauto.
- unfold c102_facts. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [|exact I]. split; [lia | split; [exact Hal16 | lia]].
Qed.
Lemma c102_SOff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. apply bv_eq. rewrite denot_SOff, Z.add_0_r. apply zcanon_id. unfold M64. apply u64_range.
Qed.
(* a run whose write windows all lie at or above YM05.alloc_ceiling (the stack) leaves every byte below it as it was *)
Lemma c102_frame_below : forall segs E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> (forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a) ->
  forall a, 0 <= a < YM05.alloc_ceiling -> mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof.
intros segs E rs H m m' HF Hrs a Ha. pose proof asan_consts as (C1 & _). unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. intros Hw. pose proof (Hrs a Hw). lia.
Qed.
End e.

(* ---- the alloc.c ledger across memory that agrees below YM05.alloc_ceiling (S911Kit.v :133-159 s911_ledger_keep,
   restated for the #102 prh_ledger: its seven cells - g_live, g_peak, g_count, g_fail_at, g_ran_out and #102's g_most
   and g_own_ran_out - are image statics, every harness head lies in a live allocator block, and all of them are below
   YM05.alloc_ceiling (AR_laws_x's blocks law). The hypothesis is read through PRH_Base.v's named projections. ---- *)
Section l. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x segs B ARx cf_head.
Lemma c102_val_mem_keep : forall (m m' : word -> option byte) a (n : nat) v,
  val_mem segs m a n v -> (forall k, (k < n)%nat -> mbyte segs m' (a + Z.of_nat k) = mbyte segs m (a + Z.of_nat k)) ->
  val_mem segs m' a n v.
Proof. intros m m' a n v Hv Hk k Hkn. rewrite (Hk k Hkn). exact (Hv k Hkn). Qed.
Lemma c102_ledger_keep : forall ly S Hp (W : world segs) mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < YM05.alloc_ceiling -> mbyte segs (mrestrict (w_H W) mem') a = mbyte segs (mrestrict (w_H W) mem) a) ->
  prh_ledger (PI := prh_img_A) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HL Hm.
pose proof (prh_ledger_live (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as G1.
pose proof (prh_ledger_peak (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as G2.
pose proof (prh_ledger_count (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as G3.
pose proof (prh_ledger_fail (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as G4.
pose proof (prh_ledger_ran (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as G5.
pose proof (prh_ledger_most (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as (G6 & G6r).
pose proof (prh_ledger_own (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as (G7 & G7r).
pose proof (prh_ledger_bounds (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as GB.
pose proof (prh_ledger_nodup (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as HN.
pose proof (prh_ledger_blocks (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as HF.
pose proof (prh_ledger_heads (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as HP.
pose proof asan_consts as (C1 & _).
assert (VB : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= YM05.alloc_ceiling ->
  val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W) mem') a n v).
{ intros a n v Ha Hb Hv. apply (c102_val_mem_keep _ _ a n v Hv). intros k Hk. apply Hm. lia. }
unfold prh_ledger, prh_glob, prh_most, prh_own.
cbn [pi_g_live pi_gz_live pi_g_peak pi_gz_peak pi_g_count pi_gz_count pi_g_fail pi_gz_fail pi_g_ran_out pi_gz_ran_out
  pi_g_most pi_gz_most pi_g_own_ran_out pi_gz_own_ran_out prh_img_A] in G1, G2, G3, G4, G5, G6, G7 |- *.
split.
{ split; [apply VB; [lia | cbn; lia | exact G1]|].
  split; [apply VB; [lia | cbn; lia | exact G2]|].
  split; [apply VB; [lia | cbn; lia | exact G3]|].
  split; [apply VB; [lia | cbn; lia | exact G4]|].
  split; [apply VB; [lia | cbn; lia | exact G5]|].
  split; [split; [apply VB; [lia | cbn; lia | exact G6] | exact G6r]|].
  split; [split; [apply VB; [lia | cbn; lia | exact G7] | exact G7r]|].
  exact GB. }
split; [exact HN|]. split; [|exact HP].
eapply Forall_impl; [|exact HF]. intros [a k] (Hk & Hin & Hhp & Hal & Hv). cbn [fst snd] in *.
destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) HAR Hin) as (H16 & H4096 & Hc & _).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hr : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
pose proof (@alloc_ceiling_val rc) as [_ Hac].
split; [exact Hk|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact Hal|].
apply VB; [lia | | exact Hv]. change (Z.of_nat 8) with 8.
(* the head and the ceiling are 16-aligned, so a head below the ceiling ends 16 bytes below it at the latest *)
destruct (proj1 (Z.mod_divide (a - cf_head) 16 ltac:(lia)) H16) as [q Hq].
destruct (proj1 (Z.mod_divide YM05.alloc_ceiling 4096 ltac:(lia)) Hac) as [r Hr2].
rewrite Hq in Hc |- *. rewrite Hr2 in Hc |- *. lia.
Qed.
End l.

(* ---- (4) the run and branch tactics (S911Kit.v :163-209; cgif YCbq.v aj_run / aj_run_to at YCbqG's SRr_run_AJx),
   with the memnorm keep threaded: MN : P -> memnorm segs (ms_mem ms) for the run's start state ms becomes
   MN : P -> memnorm segs (ms_mem ms') for its end state ms' ---- *)
Ltac c102_run tblok HS HJ MN :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let K := fresh "MNK" in
    lazymatch type of MN with
    | ?P -> _ =>
      assert (K : forall m', frame_of E (ss_mem ss) (ms_mem ms) m' -> P -> YAkMemnorm.memnorm segs m')
        by (let m' := fresh in let Hf := fresh in let H0 := fresh in
            intros m' Hf H0; exact (YGcallMxmn.memnorm_frame_of segs (w_H W) E ss ms m' (MN H0) HS Hf))
    end;
    clear MN;
    lazymatch type of tblok with
    | table_ok _ ?tbl =>
      let r := eval vm_compute in (sym_runN segs tbl FUEL ss) in
      lazymatch r with
      | (?ss', ?st) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN segs tbl FUEL ss = (ss', st)) by (vm_compute; reflexivity);
        let HL := lazymatch goal with H : AR_laws_x _ _ _ _ |- _ => H end in
        let HSL := lazymatch goal with H : forall a, in_img _ a -> 0 <= a < kLowMemEnd |- _ => H end in
        let HWX := lazymatch goal with H : wx_segs_nowrap _ |- _ => H end in
        eapply (SRr_run_AJx segs _ _ _ HL HSL tbl tblok HWX W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HJ);
        [ clear Hrun
        | clear Hrun HS HJ;
          let ms' := fresh "ms" in let mat' := fresh "mat" in
          let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
          intros ms' mat' HS HJ HF HFr HG;
          pose proof (K _ HF) as MN; clear K;
          cbn [ms_mem mkst] in HF, HFr, HG, HJ, MN;
          try match type of HS with context [restrict _ ?msn] =>
            repeat match goal with
            | old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
            end
          end;
          srr_norm_model ]
      end
    end
  end.
(* the state stops at a branch it cannot decide: split on it *)
Ltac c102_branch tbl HS :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_step segs tbl ss) in
    lazymatch r with
    | SStop (SR_branch ?c ?a ?b) =>
      apply (SRr_sym_branch segs W E ss ms _ _ c a b HS); clear HS
    | _ => fail "c102_branch: not stopped at a branch:" r
    end
  end.
