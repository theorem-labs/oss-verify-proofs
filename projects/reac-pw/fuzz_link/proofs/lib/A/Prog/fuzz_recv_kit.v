(* fuzz_recv on image A: the steps every part file of its walk takes (lib/A/Prog/fuzz_recv_defs.v names the
   states and the invariant).
   - rv_sp_bounds: the frame lies in the journal's window, above the allocator's ceiling;
   - rv_E_reg, rv_E_ext, rv_E_env: the atoms of a fresh symbolic state;
   - rv_st_ok: a fresh symbolic state `rv_ss pc rs ex` at a machine state that satisfies rv_inv: the frame region
     from the eleven frame words, the other regions and facts from the caller of the lemma.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk fuzz_recv_c fuzz_recv_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Notation W := (c_W c).
#[local] Notation memc := (c_memc c).

(* the frame [rv_sp - 96, rv_sp) and the callees' windows below it lie in the journal's window, above the ceiling *)
Lemma rv_sp_bounds :
  alloc_ceiling <= c_sp0 c - c_STK c /\ c_sp0 c - c_STK c <= rv_sp c - FUZZ_RECV_AK /\ rv_sp c <= c_sp0 c /\
  c_sp0 c + c_XO c <= 2 ^ 47 /\ rv_sp c mod 16 = 0 /\ 0 <= c_XO c.
Proof.
  destruct HC as ((HJ & _ & _ & _ & _ & _ & _ & H16 & Hwlo & Hwhi & _) & _).
  destruct HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  unfold rv_sp. lia.
Qed.

Lemma rv_E_reg : forall regs n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (rv_E c regs) n = getr regs r.
Proof.
  intros regs n r Hn Hr. unfold rv_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs _ n r Hr).
Qed.

Lemma rv_E_ext : forall regs j, (j < 11)%nat -> ew (rv_E c regs) (32 + j) = nth j (rv_ext c) (Z_to_bv 64 0).
Proof.
  intros regs j Hj. unfold rv_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ j).
Qed.

Lemma rv_E_env : forall regs, img_env VAL A_LIM (rv_E c regs).
Proof. intros regs. unfold rv_E. apply Eimg_env. Qed.

(* the frame region of rv_ss, from the eleven frame words *)
Lemma rv_fr_ok : forall regs mem md,
  rv_inv SK B c regs mem md ->
  region_ok SEGS (rv_E c regs) (rdW (c_W c) mem) rv_fr.
Proof.
  intros regs mem md (_ & _ & _ & Hsp & _ & _ & _ & _ & HFV & _).
  destruct rv_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hsp96 : 0 <= rv_sp c - 96 < 2 ^ 64).
  { clear - Hceil Hlo Hhi H47 C1a HXO0. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in Hlo. lia. }
  assert (Ub : base_val (rv_E c regs) (Some 2%nat) = rv_sp c - 96).
  { cbn [base_val]. rewrite (rv_E_reg regs 2 2%bv ltac:(lia) eq_refl). rewrite Hsp.
    unfold w64. rewrite unsigned_lit_small by exact Hsp96. reflexivity. }
  unfold rv_fr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *; lia|].
  split; [lia|]. split; [intros o Ho; lia|].
  unfold rv_frame_vals in HFV.
  repeat (let H := fresh "HV" in inversion HFV as [|? ? H HFV']; subst; clear HFV; rename HFV' into HFV;
          cbn [fst snd] in H).
  clear HFV.
  repeat match goal with H : val_mem _ _ (_ + ?o) 8 (bv_unsigned ?w) |- _ =>
    lazymatch goal with |- Forall _ (YP09.mkChunk o (CVal 8 (SOff ?n 0)) :: _) =>
      apply Forall_cons; [|clear H];
      [ apply (chunk_ok_val SEGS (rv_E c regs) _ (rv_sp c - 96) o 8 (SOff n 0) (bv_unsigned w));
        [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
          replace n with (32 + (n - 32))%nat by reflexivity;
          rewrite (rv_E_ext regs (n - 32)) by (cbv; lia); unfold rv_ext; cbn [nth Nat.sub];
          rewrite Z_to_bv_bv_unsigned; reflexivity
        | pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw;
          change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
        | cbn; lia
        | exact H ] |]
    end
  end.
  apply Forall_nil.
Qed.

(* A FRESH SYMBOLIC STATE at a machine state that satisfies rv_inv *)
Lemma rv_st_ok : forall regs mem md pc rs ex,
  rv_inv SK B c regs mem md ->
  getr regs 19 = w64 SHADOW_OFF ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (rv_E c regs) (rdW (c_W c) mem)) rs ->
  all_disjoint (rv_E c regs) rv_fr rs -> pairwise_disjoint (rv_E c regs) rs ->
  atoms_ok (rv_E c regs) ex ->
  st_ok_pi SEGS VAL (rv_E c regs) (rv_ss pc rs ex)
    (restrict (w_H (c_W c)) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros regs mem md pc rs ex HI H19 Hwf Hrs Hd1 Hd2 Hex.
  pose proof HI as (_ & _ & _ & Hsp & _).
  destruct rv_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO0).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  rewrite restrict_mkst_fx. unfold rv_ss. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - cbn [regions_wf]. rewrite Hwf. vm_compute. reflexivity.
  - apply Forall_cons; [exact (rv_fr_ok regs mem md HI) | exact Hrs].
  - cbn [pairwise_disjoint]. split; [exact Hd1 | exact Hd2].
  - split; [|split; exact I]. unfold rv_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (rv_E_reg regs 2 2%bv ltac:(lia) eq_refl), (rv_E_reg regs 19 19%bv ltac:(lia) eq_refl).
    rewrite Hsp, H19. unfold w64.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF, FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *; lia).
    change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *.
    refine (conj (conj _ (conj _ _)) (conj (conj _ (conj _ _)) Hex)); lia.
Qed.

(* ---- what the call's premises say of the buffer, g_nl and errno ---- *)
Lemma rv_pre_facts :
  0 < rv_buf c /\ NL_CHUNK_MAX <= rv_len c /\ amem_range (rv_buf c) (rv_len c) /\
  apart_gnl LA_G_NL (rv_buf c) (rv_len c) /\ apart_frame (c_regs0 c) FUZZ_RECV_AK (rv_buf c) (rv_len c) /\
  apart_frame (c_regs0 c) FUZZ_RECV_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4 /\
  0 <= as_errno B /\ as_errno B + 4 <= kLowMemEnd.
Proof.
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & Hefr & Hegn & Hlen & Hb0 & _ & Hamr & _ & _ & Hbg & Hbf).
  pose proof (proj1 (pal_env B TL)) as [He0 He1].
  unfold rv_buf, rv_len. tauto.
Qed.

(* a byte of the shadow band is a byte the call keeps *)
Lemma rv_shadow_kept : forall regs mem md, rv_inv SK B c regs mem md ->
  forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W) mem s = aview SEGS (w_H W) memc s.
Proof.
  intros regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & _ & UN & _) s Hs.
  destruct rv_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO0).
  destruct rv_pre_facts as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  apply UN; [lia | lia |].
  unfold rv_ewr, amem_range, LA_G_NL, NK_NEXT, NK_MISUSE in *. intros [H|[H|[H|H]]]; lia.
Qed.

Lemma rv_ra_kept : forall regs mem md p n, rv_inv SK B c regs mem md ->
  0 <= p -> p + n <= kHighMemEnd ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n.
Proof.
  intros regs mem md p n HI Hp Hn H x Hx. destruct (H x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  rewrite (rv_shadow_kept regs mem md HI); [exact Hsv|].
  unfold shadow_of_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF, kHighMemEnd in *.
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono x (2 ^ 47) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma rv_hull_kept : forall regs mem md p n, rv_inv SK B c regs mem md ->
  0 <= p -> p + n <= kHighMemEnd -> 0 < n ->
  shadow_hull_vis (aview SEGS (w_H W) memc) p n -> shadow_hull_vis (aview SEGS (w_H W) mem) p n.
Proof.
  intros regs mem md p n HI Hp Hn Hn0 H sx Hsx. rewrite (rv_shadow_kept regs mem md HI); [exact (H sx Hsx)|].
  unfold shadow_addr, kLowMemEnd, kHighShadowEnd, SHADOW_OFF, kHighMemEnd in *.
  pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (p + n - 1) (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma rv_hull_sub : forall rd p n p' n',
  shadow_hull_vis rd p n -> p <= p' -> p' + n' <= p + n -> 0 < n' -> shadow_hull_vis rd p' n'.
Proof.
  intros rd p n p' n' H H1 H2 H3 sx Hsx. apply H.
  pose proof (shadow_mono p p' H1). pose proof (shadow_mono (p' + n' - 1) (p + n - 1) ltac:(lia)).
  pose proof (Z.div_le_mono (shadow_addr p) (shadow_addr p') 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_le_mono (shadow_addr (p' + n' - 1)) (shadow_addr (p + n - 1)) 8 ltac:(lia) ltac:(lia)).
  lia.
Qed.

(* a val_mem fact moves with the bytes it reads *)
Lemma val_mem_kept : forall H (m m' : word -> option byte) a (n : nat) v,
  (forall k, 0 <= k < Z.of_nat n -> aview SEGS H m' (a + k) = aview SEGS H m (a + k)) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
  intros H m m' a n v Heq HV k Hk. rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat k)); [exact (HV k Hk)|].
  apply Heq. lia.
Qed.

Lemma rv_frame_offs : forall o w, In (o, w) (rv_frame_vals c) -> 8 <= o <= 88.
Proof.
  intros o w Hin. unfold rv_frame_vals in Hin.
  repeat (destruct Hin as [Hq|Hin]; [injection Hq as <- _; lia|]). destruct Hin.
Qed.

(* THE INVARIANT ACROSS A STEP that writes only below the frame (the callees' windows) and bytes of rv_ewr *)
Lemma rv_inv_step : forall regs mem md regs' mem' md' (Zs : Z -> Prop),
  rv_inv SK B c regs mem md ->
  ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
    (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) W mem' md' (c_k c) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, Zs a -> (rv_sp c - FUZZ_RECV_AK <= a < rv_sp c - 96) \/ rv_ewr B c a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
  rv_inv SK B c regs' mem' md'.
Proof.
  intros regs mem md regs' mem' md' Zs (HJ & Hfd & Hfs & Hsp & Hgp & Htp & H26 & H27 & HFV & UN & PR)
    HJ' Hfd' Hfs' UN' HZs PR' E2 E3 E4 E26 E27.
  destruct rv_sp_bounds as (Hceil & Hlo & Hhi & H47 & H16 & HXO0).
  destruct rv_pre_facts as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HnZ : forall a, rv_sp c - 96 <= a < rv_sp c -> ~ Zs a).
  { intros a Ha HZ. destruct (HZs a HZ) as [H|H]; [lia|].
    unfold rv_ewr, apart_frame, rv_buf, rv_len, rv_sp, LA_G_NL, NK_NEXT, NK_MISUSE, FUZZ_RECV_AK,
      FUZZ_RECV_AFRAME, ESTACK in *.
    destruct H as [H|[H|[H|H]]]; lia. }
  split; [exact HJ'|]. split; [congruence|]. split; [congruence|].
  split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
  split.
  { rewrite Forall_forall in HFV |- *. intros [o w] Hin. cbn [fst snd].
    pose proof (rv_frame_offs o w Hin) as Ho. pose proof (HFV (o, w) Hin) as HV. cbn [fst snd] in HV.
    apply (val_mem_kept (w_H W) mem mem'); [|exact HV].
    intros k Hk. cbn in Hk. apply UN'; [unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *; lia|].
    apply HnZ. lia. }
  split.
  { intros a Ha Hw He.
    assert (HZ : ~ Zs a) by (intros HZ; destruct (HZs a HZ) as [H|H]; [lia | exact (He H)]).
    rewrite (UN' a Ha HZ). exact (UN a Ha Hw He). }
  intros a Hp. exact (PR' a (PR a Hp)).
Qed.
End w.
