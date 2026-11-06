(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
Import ListNotations.
Open Scope Z_scope.

Definition A0_asan_memset : Z := 0x56f30.
Definition A0_asan_memcpy : Z := 0x56a94.
Definition A0_asan_memmove : Z := 0x57170.
Definition A0_stack_malloc (k : Z) : Z := match k with 0 => 0x3ebd0 | 1 => 0x3ed44 | 2 => 0x3eed4 | 3 => 0x3f070 | _ => 0x3f21c end.
Definition A0_set_shadow_f5 : Z := 0x5a5d4.

Definition A0_RT_STACK : Z := 4096.

Notation A0_FS_SIZE := 11571200%Z.
Notation A0_FS_SHSIZE := 1446400%Z.
Notation A0_FS_FRAMES := 36864%Z.

Section C.
Context {HC : HasCeiling}.

Definition asan_memset_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P c n lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(P, P + n); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' P [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))]
    /\ stk asegs m' lo q /\ asan_env asegs m'.
Definition asan_memset_stmt : Prop :=
  forall (P c n lo q : Z) (junk : list byte) (n8 : nat)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m P [CB (Z.to_nat n) junk] -> 0 <= n -> 0 <= c < 256 -> 0x609000 <= P -> P + n <= alloc_ceiling -> app_mem P n ->
  rw_cells asegs m (sh (P - P mod 8)) (shadow_zero_cells n8) -> P mod 8 + n <= 8 * Z.of_nat n8 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz P -> a1 = wz c -> a2 = wz n ->
  evt asegs (asan_memset_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc P c n lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz A0_asan_memset) fc None m (seg_rom asegs)).

Record fframe := mkFF { ff_class : Z; ff_addr : Z; ff_flag : Z }.

Definition FB_of (k : Z) : Z :=
  match k with 0 => 64 | 1 => 128 | 2 => 256 | 3 => 512 | 4 => 1024 | 5 => 2048 | 6 => 4096 | 7 => 8192 | 8 => 16384 | 9 => 32768 | _ => 65536 end.
Definition SB_of (k : Z) : Z :=
  match k with 0 => 8 | 1 => 16 | 2 => 32 | 3 => 64 | 4 => 128 | 5 => 256 | 6 => 512 | 7 => 1024 | 8 => 2048 | 9 => 4096 | _ => 8192 end.
Definition ff_size (f : fframe) : Z := FB_of (ff_class f).
Definition ff_shsize (f : fframe) : Z := SB_of (ff_class f).

Definition lb (L : list fframe) (A n : Z) : Prop := exists g, In g L /\ ff_addr g <= A /\ A + n <= ff_addr g + ff_size g.
Definition ls (L : list fframe) (A n : Z) : Prop := exists g, In g L /\ sh (ff_addr g) <= A /\ A + n <= sh (ff_addr g) + ff_shsize g.
Definition lf (L : list fframe) (A : Z) : Prop := exists g, In g L /\ A = ff_flag g.
Definition in_pieces (g : fframe) (a : Z) : Prop :=
  (ff_addr g <= a < ff_addr g + ff_size g) \/ (sh (ff_addr g) <= a < sh (ff_addr g) + ff_shsize g) \/ a = ff_flag g.

Definition ff_apart (a b : fframe) : Prop :=
  (ff_addr a + ff_size a <= ff_addr b \/ ff_addr b + ff_size b <= ff_addr a)
  /\ (sh (ff_addr a) + ff_shsize a <= sh (ff_addr b) \/ sh (ff_addr b) + ff_shsize b <= sh (ff_addr a))
  /\ (ff_flag a + 1 <= ff_flag b \/ ff_flag b + 1 <= ff_flag a).

Definition fsenv_cls (FSB0 : Z) (iv : ivl) : Prop :=
  alloc_ceiling <= fst iv
  \/ (FSB0 <= fst iv /\ snd iv <= FSB0 + A0_FS_SIZE)
  \/ (0x7fff7000 <= fst iv /\ snd iv <= 0x10007fff8000)
  \/ (0x10000 <= fst iv /\ snd iv <= 0x609000 /\ env_safe [iv]).

Record fs_if := mkFS {
  fsstate : Type;
  fs_live : fsstate -> list fframe;
  RFAKE : fsstate -> mem -> Prop;
  FSENV : mem -> Prop;
  fs_after_malloc : fsstate -> Z -> fsstate * fframe;
  fs_after_release : fsstate -> fsstate;
  FSB : Z;

  fsb_ok : 0x609000 <= FSB /\ FSB + A0_FS_SIZE <= alloc_ceiling /\ app_mem FSB A0_FS_SIZE /\ FSB mod 4096 = 0
           /\ (FSB + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= FSB);

  live_wf : forall st m, RFAKE st m ->
      Forall (fun g => 0 <= ff_class g <= 10 /\ FSB + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + ff_size g <= FSB + A0_FS_SIZE
                       /\ ff_addr g mod 64 = 0 /\ FSB + 4096 <= ff_flag g /\ ff_flag g + 1 <= FSB + A0_FS_FRAMES) (fs_live st);

  rfake_frame : forall st m m' W,
      RFAKE st m -> munch W m m' -> wmono asegs m m' ->
      Forall (fun iv => ((snd iv <= FSB \/ FSB + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh FSB \/ sh FSB + A0_FS_SHSIZE <= fst iv))
                        \/ lb (fs_live st) (fst iv) (snd iv - fst iv) \/ ls (fs_live st) (fst iv) (snd iv - fst iv)) W ->
      RFAKE st m';

  new_facts : forall st k m, RFAKE st m -> 0 <= k <= 10 ->
      let g := snd (fs_after_malloc st k) in
      ff_class g = k /\ FSB + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + FB_of k <= FSB + A0_FS_SIZE /\ ff_addr g mod 64 = 0
      /\ FSB + 4096 <= ff_flag g /\ ff_flag g + 1 <= FSB + A0_FS_FRAMES
      /\ Forall (ff_apart g) (fs_live st);

  release : forall st ff rest m m' cs,
      RFAKE st m -> fs_live st = ff :: rest ->
      munch [(ff_flag ff, ff_flag ff + 1)] m m' -> wmono asegs m m' ->
      rw_cells asegs m' (ff_flag ff) [C1 (Z_to_bv 8 0)] ->
      rw_cells asegs m' (sh (ff_addr ff)) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize ff)))) ->
      rw_cells asegs m' (ff_addr ff) cs -> Z.of_nat (cells_size cs) = ff_size ff ->
      RFAKE (fs_after_release st) m' /\ fs_live (fs_after_release st) = rest;

  rfake_frame_m : forall st m m' W,
      RFAKE st m -> munch W m m' ->
      Forall (fun iv => ((snd iv <= FSB \/ FSB + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh FSB \/ sh FSB + A0_FS_SHSIZE <= fst iv))
                        \/ lb (fs_live st) (fst iv) (snd iv - fst iv) \/ ls (fs_live st) (fst iv) (snd iv - fst iv)) W ->
      RFAKE st m';

  rfake_frame_g : forall st m m' W,
      RFAKE st m -> gmunch W m m' -> wmono asegs m m' ->
      Forall (fun iv => ((snd iv <= FSB \/ FSB + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh FSB \/ sh FSB + A0_FS_SHSIZE <= fst iv))
                        \/ lb (fs_live st) (fst iv) (snd iv - fst iv) \/ ls (fs_live st) (fst iv) (snd iv - fst iv)) W ->
      RFAKE st m';

  fsenv_frame : forall m m' W, FSENV m -> munch W m m' -> Forall (fsenv_cls FSB) W -> FSENV m'
}.

Variable FI : fs_if.
Local Notation fsst := (fsstate FI).

Definition fs_newff (st : fsst) (k : Z) : fframe := snd (fs_after_malloc FI st k).
Definition fs_next (st : fsst) (k : Z) : fsst := fst (fs_after_malloc FI st k).
Definition fs_F (st : fsst) (k : Z) : Z := ff_addr (fs_newff st k).
Definition fs_FL (st : fsst) (k : Z) : Z := ff_flag (fs_newff st k).

Definition in_live (st : fsst) (A n : Z) : Prop :=
  lb (fs_live FI st) A n \/ ls (fs_live FI st) A n \/ (lf (fs_live FI st) A /\ n = 1).

Definition fkeep (W : list ivl) (st : fsst) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> (exists g, In g (fs_live FI st) /\ in_pieces g a) -> outside W a -> gkeep m m' (wa a).

#[using="Type"] Lemma fkeep_refl : forall W st m, fkeep W st m m.
Proof. intros W st m a _ _ _; apply gkeep_refl. Qed.
#[using="Type"] Lemma fkeep_trans : forall W st m1 m2 m3, fkeep W st m1 m2 -> fkeep W st m2 m3 -> fkeep W st m1 m3.
Proof. intros W st m1 m2 m3 H1 H2 a Ha Hg Ho. eapply gkeep_trans; [apply H1| apply H2]; assumption. Qed.

#[using="Type"] Lemma fkeep_mrd : forall W st m m' a b, fkeep W st m m' -> 0 <= a < 2^64 -> (exists g, In g (fs_live FI st) /\ in_pieces g a) -> outside W a ->
  mrd asegs m (wa a) = Some b -> mrd asegs m' (wa a) = Some b.
Proof. intros W st m m' a b FK Ha Hg Ho Hr. exact (gkeep_mrd m m' (wa a) b (FK a Ha Hg Ho) Hr). Qed.

#[using="Type"] Lemma fkeep_weaken : forall W W' st st' m m',
  fkeep W st m m' -> sub_fp W W' -> (forall g, In g (fs_live FI st') -> In g (fs_live FI st)) -> fkeep W' st' m m'.
Proof.
  intros W W' st st' m m' H HW HL a Ha (g & Hg & Hp) Ho. apply H; [exact Ha| | apply HW; exact Ho].
  exists g. split; [apply HL; exact Hg| exact Hp].
Qed.
#[using="Type"] Lemma fkeep_live_eq : forall W st st' m m', fkeep W st m m' -> fs_live FI st' = fs_live FI st -> fkeep W st' m m'.
Proof. intros W st st' m m' H E. eapply fkeep_weaken; [exact H| intros x Hx; exact Hx| intros g Hg; rewrite <- E; exact Hg]. Qed.
#[using="Type"] Lemma fkeep_live_cons : forall W st st' g0 m m', fkeep W st' m m' -> fs_live FI st' = g0 :: fs_live FI st -> fkeep W st m m'.
Proof. intros W st st' g0 m m' H E. eapply fkeep_weaken; [exact H| intros x Hx; exact Hx| intros g Hg; rewrite E; right; exact Hg]. Qed.

Definition fk_ok (W : list ivl) (st : fsst) (iv : ivl) : Prop :=
  inside W (fst iv) (snd iv - fst iv)
  \/ ((snd iv <= FSB FI \/ FSB FI + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= fst iv))
  \/ Forall (fun g => (snd iv <= ff_addr g \/ ff_addr g + ff_size g <= fst iv)
                      /\ (snd iv <= sh (ff_addr g) \/ sh (ff_addr g) + ff_shsize g <= fst iv)
                      /\ (snd iv <= ff_flag g \/ ff_flag g + 1 <= fst iv)) (fs_live FI st).

#[using="Type"] Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros a b H. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

#[using="Type"] Lemma live_pieces_inside : forall st m g a, RFAKE FI st m -> In g (fs_live FI st) -> in_pieces g a ->
  (FSB FI <= a < FSB FI + A0_FS_SIZE) \/ (sh (FSB FI) <= a < sh (FSB FI) + A0_FS_SHSIZE).
Proof.
  intros st m g a HR Hg Hp. pose proof (live_wf FI st m HR) as W. rewrite Forall_forall in W. specialize (W g Hg).
  destruct W as (Wk & W1 & W2 & W3 & W4 & W5). pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4).
  unfold in_pieces, ff_size, ff_shsize in *.
  assert (SBF : SB_of (ff_class g) * 8 = FB_of (ff_class g)).
  { unfold SB_of, FB_of. destruct (ff_class g) as [|p|p]; try reflexivity; repeat (destruct p; try reflexivity). }
  unfold sh, SHADOW_OFF in *.
  destruct Hp as [Hp|[Hp|Hp]]; [left; lia| right; lia| left; lia].
Qed.

#[using="Type"] Lemma outside_of_forall : forall W a,
  Forall (fun iv : ivl => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn; [exact I|].
  inversion H as [|x l H1 H2]; subst. cbn in H1. split; [exact H1| apply IH; exact H2].
Qed.

#[using="Type"] Lemma fkeep_of_munch : forall W Ws st st' m m0 m',
  RFAKE FI st' m0 -> (forall g, In g (fs_live FI st) -> In g (fs_live FI st')) ->
  munch Ws m m' -> Forall (fk_ok W st) Ws -> fkeep W st m m'.
Proof.
  intros W Ws st st' m m0 m' HR HL MU OK a Ha (g & Hg & Hp) Ho.
  apply gkeep_of_eq. apply MU. rewrite wa_unsigned by lia. apply outside_of_forall.
  eapply Forall_impl; [| exact OK]. intros [lo hi] K. unfold fk_ok, fst, snd in K. unfold fst, snd.
  destruct K as [K|[K|K]].
  - intros Hr. apply (inside_not_outside W lo (hi - lo) a K); [lia| exact Ho].
  - pose proof (live_pieces_inside st' m0 g a HR (HL g Hg) Hp) as X. lia.
  - rewrite Forall_forall in K. specialize (K g Hg). unfold fst, snd in K. unfold in_pieces in Hp. lia.
Qed.

#[using="Type"] Lemma bytes_at_fkeep : forall W st m m' A bs,
  bytes_at asegs m A bs -> fkeep W st m m' -> in_live st A (Z.of_nat (length bs)) ->
  disjoint_from W A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros W st m m' A bs (Ha & Hl & HB) FK IL HD. split; [exact Ha|]. split; [exact Hl|].
  intros i Hi. pose proof (HB i Hi) as Hr. destruct (nth_error bs i) as [b|] eqn:En; [| exfalso; apply nth_error_None in En; lia].
  eapply (fkeep_mrd W st m m' _ b FK); [lia| | eapply disjoint_outside; [exact HD| lia]| exact Hr].
  unfold in_live, lb, ls, lf, in_pieces in *.
  destruct IL as [(g & Hg & HP & HQ)|[(g & Hg & HP & HQ)|((g & Hg & HP) & Hn)]]; exists g; (split; [exact Hg| lia]).
Qed.
#[using="Type"] Lemma rw_cells_fkeep : forall W st m m' A cs,
  rw_cells asegs m A cs -> fkeep W st m m' -> wmono asegs m m' -> in_live st A (Z.of_nat (cells_size cs)) ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros W st m m' A cs [[Hwf HB] HW] FK WM IL HD. split; [split; [exact Hwf|]|].
  - eapply bytes_at_fkeep; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply wr_at_transport; eauto.
Qed.

#[using="Type"] Lemma lb_sub : forall L A n A' n', lb L A n -> A <= A' -> A' + n' <= A + n -> lb L A' n'.
Proof. intros L A n A' n' (g & Hg & H1 & H2) H3 H4. exists g. split; [exact Hg| lia]. Qed.
#[using="Type"] Lemma ls_sub : forall L A n A' n', ls L A n -> A <= A' -> A' + n' <= A + n -> ls L A' n'.
Proof. intros L A n A' n' (g & Hg & H1 & H2) H3 H4. exists g. split; [exact Hg| lia]. Qed.
#[using="Type"] Lemma lb_mono : forall L L' A n, lb L A n -> (forall g, In g L -> In g L') -> lb L' A n.
Proof. intros L L' A n (g & Hg & H) HL. exists g. split; [apply HL; exact Hg| exact H]. Qed.
#[using="Type"] Lemma ls_mono : forall L L' A n, ls L A n -> (forall g, In g L -> In g L') -> ls L' A n.
Proof. intros L L' A n (g & Hg & H) HL. exists g. split; [apply HL; exact Hg| exact H]. Qed.
#[using="Type"] Lemma lf_mono : forall L L' A, lf L A -> (forall g, In g L -> In g L') -> lf L' A.
Proof. intros L L' A (g & Hg & H) HL. exists g. split; [apply HL; exact Hg| exact H]. Qed.
#[using="Type"] Lemma sub_eq : forall (L L' : list fframe), L' = L -> forall g, In g L -> In g L'.
Proof. intros L L' -> g Hg; exact Hg. Qed.
#[using="Type"] Lemma sub_cons : forall (L L' : list fframe) g0, L' = g0 :: L -> forall g, In g L -> In g L'.
Proof. intros L L' g0 -> g Hg; right; exact Hg. Qed.
#[using="Type"] Lemma lb_new : forall L L' g0, L' = g0 :: L -> lb L' (ff_addr g0) (ff_size g0).
Proof. intros L L' g0 ->. exists g0. split; [left; reflexivity| lia]. Qed.
#[using="Type"] Lemma ls_new : forall L L' g0, L' = g0 :: L -> ls L' (sh (ff_addr g0)) (ff_shsize g0).
Proof. intros L L' g0 ->. exists g0. split; [left; reflexivity| lia]. Qed.
#[using="Type"] Lemma lf_new : forall L L' g0, L' = g0 :: L -> lf L' (ff_flag g0).
Proof. intros L L' g0 ->. exists g0. split; [left; reflexivity| reflexivity]. Qed.

#[using="Type"] Lemma new_frame_facts : forall st k m F SF FL, RFAKE FI st m -> 0 <= k <= 10 ->
  F = fs_F st k -> SF = sh F -> FL = fs_FL st k ->
  ff_class (fs_newff st k) = k
  /\ FSB FI + A0_FS_FRAMES <= F /\ F + FB_of k <= FSB FI + A0_FS_SIZE /\ F mod 64 = 0
  /\ FSB FI + 4096 <= FL /\ FL + 1 <= FSB FI + A0_FS_FRAMES
  /\ Forall (fun g => (F + FB_of k <= ff_addr g \/ ff_addr g + ff_size g <= F)
                      /\ (SF + SB_of k <= sh (ff_addr g) \/ sh (ff_addr g) + ff_shsize g <= SF)
                      /\ (FL + 1 <= ff_flag g \/ ff_flag g + 1 <= FL)) (fs_live FI st).
Proof.
  intros st k m F SF FL HR Hk -> -> ->.
  destruct (new_facts FI st k m HR Hk) as (C & A1 & A2 & A3 & A4 & A5 & AP).
  unfold fs_F, fs_FL, fs_newff in *. repeat (split; [assumption|]).
  eapply Forall_impl; [| exact AP]. intros g Hg. unfold ff_apart, ff_size, ff_shsize in Hg |- *. rewrite C in Hg. exact Hg.
Qed.

#[using="Type"] Lemma fs_shadow_apart : FSB FI + A0_FS_SIZE <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= FSB FI.
Proof. pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4). unfold app_mem, sh, SHADOW_OFF in *. lia. Qed.

#[using="Type"] Lemma SB_FB : forall k, 0 <= k <= 10 -> SB_of k * 8 = FB_of k /\ 8 <= SB_of k <= 8192.
Proof.
  intros k Hk. unfold SB_of, FB_of. destruct k as [|p|p]; [lia| |lia].
  do 4 (try destruct p as [p|p|]); cbn; lia.
Qed.

#[using="Type"] Lemma live_num : forall st m, RFAKE FI st m ->
  Forall (fun g => FSB FI + A0_FS_FRAMES <= ff_addr g /\ ff_addr g + ff_size g <= FSB FI + A0_FS_SIZE /\ ff_addr g mod 64 = 0
                   /\ FSB FI + 4096 <= ff_flag g /\ ff_flag g + 1 <= FSB FI + A0_FS_FRAMES
                   /\ ff_shsize g * 8 = ff_size g /\ 8 <= ff_shsize g <= 8192
                   /\ sh (FSB FI) <= sh (ff_addr g) /\ sh (ff_addr g) + ff_shsize g <= sh (FSB FI) + A0_FS_SHSIZE) (fs_live FI st).
Proof.
  intros st m HR. eapply Forall_impl; [| exact (live_wf FI st m HR)]. cbv beta. intros g (Wk & W1 & W2 & W3 & W4 & W5).
  pose proof (SB_FB (ff_class g) Wk) as [E R]. unfold ff_size, ff_shsize in *.
  pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4).
  repeat (split; [lia|]). unfold sh, SHADOW_OFF. split; lia.
Qed.

#[using="Type"] Lemma new_frame_fk : forall st k m F SF FL, RFAKE FI st m -> 0 <= k <= 10 ->
  F = fs_F st k -> SF = sh F -> FL = fs_FL st k ->
  forall W A n, (F <= A /\ A + n <= F + FB_of k) \/ (SF <= A /\ A + n <= SF + SB_of k) \/ (A = FL /\ n = 1) ->
  fk_ok W st (A, A + n).
Proof.
  intros st k m F SF FL HR Hk EF ESF EFL W A n HP. unfold fk_ok. right; right. unfold fst, snd.
  destruct (new_frame_facts st k m F SF FL HR Hk EF ESF EFL) as (C & A1 & A2 & A3 & A4 & A5 & AP).
  pose proof (Forall_and (live_num st m HR) AP) as X. eapply Forall_impl; [| exact X]. cbv beta. clear X AP.
  intros g ((W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9) & P1 & P2 & P3).
  pose proof fs_shadow_apart as SA. pose proof (SB_FB k Hk) as [E R].
  assert (SHF : sh (FSB FI) <= SF /\ SF + SB_of k <= sh (FSB FI) + A0_FS_SHSIZE).
  { rewrite ESF. pose proof (fsb_ok FI) as (B1 & B2 & B3 & B4). unfold sh, SHADOW_OFF. split; lia. }
  destruct HP as [HP|[HP|HP]]; (split; [lia| split; [lia| lia]]).
Qed.

#[using="Type"] Lemma lb_apart_frame : forall L A n F FB (P Q : fframe -> Prop),
  lb L A n -> Forall (fun g => (F + FB <= ff_addr g \/ ff_addr g + ff_size g <= F) /\ P g /\ Q g) L -> A + n <= F \/ F + FB <= A.
Proof. intros L A n F FB P Q (g & Hg & H1 & H2) AP. rewrite Forall_forall in AP. destruct (AP g Hg) as (X & _ & _). lia. Qed.
#[using="Type"] Lemma lb_apart_shadow : forall st m A n B k, RFAKE FI st m -> lb (fs_live FI st) A n ->
  sh (FSB FI) <= B -> B + k <= sh (FSB FI) + A0_FS_SHSIZE -> A + n <= B \/ B + k <= A.
Proof.
  intros st m A n B k HR (g & Hg & H1 & H2) HB1 HB2. pose proof (live_num st m HR) as W. rewrite Forall_forall in W.
  destruct (W g Hg) as (W1 & W2 & _). pose proof fs_shadow_apart. lia.
Qed.
#[using="Type"] Lemma lb_apart_flag : forall st m A n FL, RFAKE FI st m -> lb (fs_live FI st) A n ->
  FSB FI + 4096 <= FL -> FL + 1 <= FSB FI + A0_FS_FRAMES -> A + n <= FL \/ FL + 1 <= A.
Proof.
  intros st m A n FL HR (g & Hg & H1 & H2) HB1 HB2. pose proof (live_num st m HR) as W. rewrite Forall_forall in W.
  destruct (W g Hg) as (W1 & W2 & _). lia.
Qed.

Definition stack_malloc_post (k : Z) (st : fsst) (F SF FL FB : Z) (FBm SBn : nat) (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F_ : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (junk1 junk2 : list byte),
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(FSB FI, FSB FI + A0_FS_SIZE); (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE); (lo, q)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ fkeep [] st m m'
    /\ fs_live FI (fs_next st k) = fs_newff st k :: fs_live FI st /\ RFAKE FI (fs_next st k) m'
    /\ rw_cells asegs m' F [CB 24%nat junk1; C8 (wz q); CB FBm junk2; C8 (wz FL)]
    /\ rw_cells asegs m' SF (shadow_zero_cells SBn)
    /\ rw_cells asegs m' FL [C1 (Z_to_bv 8 1)]
    /\ stk asegs m' lo q /\ asan_env asegs m'.

Definition A0_FS_DEPTH : nat := 15.
Definition fs_call_ok (st : fsst) (tp : word) (d : nat) : Prop :=
  bv_unsigned tp = 6190512 /\ (length (fs_live FI st) + d <= A0_FS_DEPTH)%nat.
#[using="Type"] Lemma fs_call_ok_le : forall st tp d d', fs_call_ok st tp d -> (d' <= d)%nat -> fs_call_ok st tp d'.
Proof. intros st tp d d' [T L] LE. split; [exact T| lia]. Qed.
#[using="Type"] Lemma fs_call_ok_push : forall st st1 tp d g, fs_call_ok st tp (S d) -> fs_live FI st1 = g :: fs_live FI st -> fs_call_ok st1 tp d.
Proof. intros st st1 tp d g [T L] E. split; [exact T|]. rewrite E. cbn [length]. lia. Qed.
#[using="Type"] Lemma fs_call_ok_live_eq : forall st st' tp d, fs_call_ok st tp d -> fs_live FI st' = fs_live FI st -> fs_call_ok st' tp d.
Proof. intros st st' tp d [T L] E. split; [exact T|]. rewrite E. exact L. Qed.

#[using="Type"] Lemma fsenv_after_stack_malloc : forall m m' lo q,
  FSENV FI m -> munch [(FSB FI, FSB FI + A0_FS_SIZE); (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE); (lo, q)] m m' -> alloc_ceiling <= lo -> FSENV FI m'.
Proof.
  intros m m' lo q FE MU HLO. eapply (fsenv_frame FI); [exact FE| exact MU|].
  pose proof (fsb_ok FI) as (B1 & B2 & _ & _ & _). pose proof alloc_ceiling_bounds as ACR.
  constructor; [right; left; cbn [fst snd]; lia|]. constructor; [| constructor; [left; exact HLO| constructor]].
  right; right; left. cbn [fst snd]. unfold sh, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
Qed.

Definition stack_malloc_stmt (k : Z) : Prop :=
  forall (st : fsst) (lo q size F SF FL FB : Z) (FBm SBn : nat)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  F = fs_F st k -> SF = sh F -> FL = fs_FL st k -> FB = FB_of k -> Z.of_nat FBm = FB - 40 -> Z.of_nat SBn = SB_of k ->
  RFAKE FI st m -> fs_call_ok st tp 1 -> FSENV FI m -> asan_env asegs m ->
  0 < size <= FB ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz size ->
  evt asegs (stack_malloc_post k st F SF FL FB FBm SBn ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz (A0_stack_malloc k)) fc None m (seg_rom asegs)).

Definition set_shadow_f5_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (SA len lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(SA, SA + len); (lo, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' SA (shadow_cells (repeat 245 (Z.to_nat len)))
    /\ stk asegs m' lo q /\ asan_env asegs m'.
Definition set_shadow_f5_stmt : Prop :=
  forall (SA len lo q : Z) (old : list cell)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F_ : bvmap 5 word) (fc : bv 32) (m : mem),
  rw_cells asegs m SA old -> Z.of_nat (cells_size old) = len -> 0 < len ->
  0x7fff8000 <= SA -> SA + len <= 0x10007fff8000 ->
  asan_env asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q < 2^64 ->
  mem_inv asegs m -> a0 = wz SA -> a1 = wz len ->
  evt asegs (set_shadow_f5_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc SA len lo m)
    (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_set_shadow_f5) fc None m (seg_rom asegs)).
End C.

Arguments fs_newff {HC} FI st k.
Arguments fs_next {HC} FI st k.
Arguments fs_F {HC} FI st k.
Arguments fs_FL {HC} FI st k.
Arguments in_live {HC} FI st A n.
Arguments fkeep {HC} FI W st m m'.
Arguments fk_ok {HC} FI W st iv.
