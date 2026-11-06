From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01 YL0g YL00 YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import
Ledger PjStruct ReaderRes EntC1_Defs EntC1_Glue round_trip_text_c check_reject_clean_starved_c
LLVMFuzzerTestOneInput_c EntryDefs EntrySR EntBase EntStg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma esq_uns : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity. Qed.

(* #102 plain pin: LLVMFuzzerTestOneInput (0x13628) opens a 112-byte frame (`addi sp, sp, -112`), and EntStg.ent_rk
   states sp = S - 112 and gp, tp, s6-s11 (x3, x4, x22-x27) kept from the entry. *)
Lemma esq_sp : forall regs0 regs, getr regs 2 = Z_to_bv 64 (spZ regs0 - 112) -> 112 <= spZ regs0 ->
  spZ regs = spZ regs0 - 112.
Proof.
  intros regs0 regs G H. pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. unfold spZ in *. rewrite G. apply esq_uns. lia.
Qed.

Lemma esq_rk : forall regs0 r1 r2, regs_preserved r1 r2 -> ent_rk regs0 r1 -> ent_rk regs0 r2.
Proof.
  intros regs0 r1 r2 RR (G2 & G3 & G4 & G22 & G23 & G24 & G25 & G26 & G27).
  split; [etransitivity; [apply (RR 2); unfold callee_saved; lia | exact G2]|].
  split; [etransitivity; [apply (RR 3); unfold callee_saved; lia | exact G3]|].
  split; [etransitivity; [apply (RR 4); unfold callee_saved; lia | exact G4]|].
  split; [etransitivity; [apply (RR 22); unfold callee_saved; lia | exact G22]|].
  split; [etransitivity; [apply (RR 23); unfold callee_saved; lia | exact G23]|].
  split; [etransitivity; [apply (RR 24); unfold callee_saved; lia | exact G24]|].
  split; [etransitivity; [apply (RR 25); unfold callee_saved; lia | exact G25]|].
  split; [etransitivity; [apply (RR 26); unfold callee_saved; lia | exact G26]|].
  etransitivity; [apply (RR 27); unfold callee_saved; lia | exact G27].
Qed.

Lemma esq_pres : forall r1 r2 r v, regs_preserved r1 r2 -> callee_saved r -> getr r1 (Z_to_bv 5 r) = v ->
  getr r2 (Z_to_bv 5 r) = v.
Proof. intros r1 r2 r v RR Hr E. rewrite (RR r Hr). exact E. Qed.

Lemma esq_gr_doc : forall x took doc t, doc <> 0 -> crcs_growth x took doc t = crcs_growth x took 1 t.
Proof. intros x took doc t H. unfold crcs_growth. rewrite (proj2 (Z.eqb_neq doc 0) H). reflexivity. Qed.

Lemma esq_after_doc : forall F b c x doc t, doc <> 0 -> crs_after_doc F b c x doc t = crs_doc_fold F b c x t.
Proof. intros F b c x doc t H. unfold crs_after_doc. rewrite (proj2 (Z.eqb_neq doc 0) H). reflexivity. Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Let AX : AllocExtra B (aa_MR API) := ent_AX B API FA.
Let FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a := ent_FG B API FA.

Lemma esq_lblk : forall L A mem md Lam peak cnt fail a k, aa_MR API L A mem md ->
  ledger B L A mem Lam peak cnt fail -> In (a, k) Lam ->
  0 <= k /\ In (a - 16, k + 16) (blocks L A) /\ 4112 <= a /\ a + k <= alloc_ceiling /\
  (forall i, - 16 <= i < k -> ~ in_img B (a + i)).
Proof.
  intros L A mem md Lam peak cnt fail a k HM HL Hin.
  pose proof (ledger_block_range B API L A mem md Lam peak cnt fail a k HM HL Hin) as (R1 & R2 & _).
  pose proof HL as (_ & _ & _ & _ & _ & FB). rewrite Forall_forall in FB.
  destruct (FB (a, k) Hin) as (Hk & Hb & _ & _). cbn [fst snd] in Hk, Hb.
  split; [exact Hk|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
  intros i Hi. exact (ledger_block_not_img B L A mem Lam peak cnt fail a k i HL Hin Hi).
Qed.

Lemma esq_rpost_blocks : forall K L A regs mem md E gone L' A' regs' mem' md',
  rpost B API K L A regs mem md E gone L' A' regs' mem' md' ->
  forall a k, In (a, k) (blocks L A) -> ~ gone a k -> In (a, k) (blocks L' A').
Proof.
  intros K L A regs mem md E gone L' A' regs' mem' md' (_ & _ & _ & _ & _ & _ & _ & UB & PA & _) a k Hin Hg.
  destruct (rg_blk_in B API HSEG AX FG L A a k Hin) as (q0 & Hq0 & <-).
  assert (Hq1 : In (q0, k) (user_blocks A')) by (apply UB; [exact Hq0 | exact Hg]).
  rewrite <- (PA q0 k Hq0 Hq1). exact (rg_blk_of B API HSEG AX FG L' A' q0 k Hq1).
Qed.

Lemma esq_rstep_rtt : forall K regs E L A mem md L' A' regs' mem' md',
  rtt_rel B API K regs E L A mem md L' A' regs' mem' md' ->
  rstep B API K (spZ regs) E (fun _ => False) L A mem md L' A' mem' md'.
Proof.
  intros K regs E L A mem md L' A' regs' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  split; [intros a k Hin _ _; exact (H5 a k Hin)|].
  split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [intros a k i Hin _ Hi He; exact (H10 a k i Hin Hi He)|].
  exact H11.
Qed.

Lemma esq_pay : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd D,
  ent_pre (fx := fx) B API F stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv B API F stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  0 < empty < 2 ^ 62 -> Permutation Lam D -> new_blks L0 A0 D ->
  0 < p /\ p + n < 2 ^ 62 /\ Z.of_nat (length pl) = n /\ Mem.bytes_at segs mem p pl /\
  (0 < n -> exists a k, In (a, k) (blocks L A) /\ ~ lin Lam (a + 16) (k - 16) /\ a <= p /\ p + n <= a + k) /\
  (forall i, 0 <= i < n ->
     ~ owned B L A (p + i) /\ ~ alloc_statics (p + i) /\ ~ (errno_addr B <= p + i < errno_addr B + 4)).
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd D
    ENT INV HEMP PL NEW.
  pose proof ENT as ((PRE & HNL & BLK & _) & SYMS & _).
  pose proof PRE as (MR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
  pose proof INV as (RS & _ & _ & _ & _ & _ & _ & PAY0 & _).
  pose proof RS as (MRc & _ & _ & _ & PSc & _).
  pose proof alloc_ceiling_val as HCV. pose proof alloc_ceiling_lt as HCL.
  pose proof (ent_errno B SYMS) as ERRB.
  assert (BY : Mem.bytes_at segs mem p pl).
  { assert (Hp0 : 0 <= p /\ p + n <= 2 ^ 64).
    { destruct PAY as [(Hn & ->)|(Hn & q & Hq & <-)]; [lia|].
      destruct (rg_blk B API HSEG AX FG L0 A0 mem0 md0 (ptr_addr L0 q) n 0 MR0
        (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) ltac:(lia)) as (_ & H1 & H2 & _). lia. }
    split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (PAY0 (Z.of_nat i) ltac:(lia)) as E1. pose proof (BLK (Z.of_nat i) ltac:(lia)) as E2.
    rewrite Nat2Z.id in E2. exact (eq_trans E1 E2). }
  destruct PAY as [(Hn & ->)|(Hn & q & Hq & <-)].
  - split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BY|]. split; [intros Hc; lia|]. intros i Hi. lia.
  - pose proof (rg_blk_of B API HSEG AX FG L0 A0 q n Hq) as Hb0.
    pose proof (PSc _ _ Hb0 Hn (fun h => h)) as HbL.
    destruct (rg_blk B API HSEG AX FG L A mem md (ptr_addr L0 q) n 0 MRc HbL ltac:(lia)) as (_ & H1 & H2 & _).
    destruct (rg_blk_in B API HSEG AX FG L A _ _ HbL) as (q' & Hq' & Eq).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BY|].
    split.
    { intros _. exists (ptr_addr L0 q), n. split; [exact HbL|]. split; [|lia].
      intros Hl. unfold lin in Hl. apply (NEW (ptr_addr L0 q + 16) (n - 16)).
      - exact (Permutation_in _ PL Hl).
      - replace (ptr_addr L0 q + 16 - 16) with (ptr_addr L0 q) by lia. replace (n - 16 + 16) with n by lia. exact Hb0. }
    intros i Hi.
    destruct (rg_blk B API HSEG AX FG L A mem md (ptr_addr L0 q) n i MRc HbL Hi) as (_ & _ & _ & Ho).
    split; [exact Ho|]. split.
    + intros Hs. apply (ax_blocks_img AX L A mem md q' n i MRc Hq' Hi). rewrite Eq.
      exact (proj1 (statics_img B API HSEG AX FG _ Hs)).
    + intros He. apply (ax_blocks_img AX L A mem md q' n i MRc Hq' Hi). rewrite Eq.
      replace (ptr_addr L0 q + i) with (errno_addr B + (ptr_addr L0 q + i - errno_addr B)) by lia.
      apply (errno_img B API HSEG AX FG ERRB). lia.
Qed.

End G.
