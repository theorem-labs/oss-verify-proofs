(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): one turn of piece A's
   loop, 0x13b04 .. the latch 0x13b78, for the i-th segment
   g = m->seg[i] (i < m->n) with SegModel.check_seg rc g = true, on any memory m with M02_inv S m0 m:
   `sw s2,0x40(sp)` (main's cell r = 0x5a, inside M02_W), reac_segconf_role(c, s3, sp + 0x40), `lw a1,0x40(sp)` (the
   role when r_role answers Some, else still 0x5a), check_role(a0, a1, s3); reac_segconf_model(c, s3),
   check_model(a0, s3); reac_segconf_ignored(c, s3), check_ignore(a0, s3); s4 = reac_segconf_role_file(c, s3),
   a1 = reac_segconf_ignore_file(c, s3), check_provenance(s4, a1, s3). Each callee runs at sp = S - 208 on the
   stack region [S - 65536, sp) (M02K.m02_stack_ok), with c's rc and m's mc read back from the current memory
   (M02K.m02_rconf / m02_mconf) and the name, the entry and the reader's pointer answers from M02_bridge; every
   callee post steps M02_inv (M02K.m02_inv_call / m02_inv_nil, ma_inv_role), and the store keeps it (ma_inv_sw).
   M02APure holds the lemmas that do not mention the image.
   Part of the proof of LLVMFuzzerTestOneInput: a turn of segment M02's piece A of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment walk lemma). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_find_c reac_segconf_role_c
  check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import M02D M02K.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
Import M02_bridge.M02Bridge.
Import check_segments.CsPure.
Import ListNotations.
Open Scope Z_scope.

Module M02APure.

Section Pure.
Variable segs : list Segment.

(** n writable bytes inside a present stack window. *)
Lemma ma_wr : forall m lo hi a n, stk segs m lo hi -> lo <= a -> a + n <= hi -> 0 <= n -> wr_at segs m a n.
Proof.
  intros m lo hi a n (H1 & H2 & H) Ha Hb Hn. split; [lia|]. split; [lia|].
  intros j Hj. exact (proj1 (H (a + j) ltac:(lia))).
Qed.

(** A pointer answer (NULL or a C string) is a 64-bit address. *)
Lemma ma_ocz_rng : forall m a o, ocstrz_at segs m a o -> 0 <= a < 2 ^ 64.
Proof.
  intros m a o H. destruct o as [s|]; cbn [ocstrz_at] in H.
  - destruct H as (_ & bs & B & _). pose proof (bytes_at_bound segs _ _ _ B) as R.
    rewrite length_app in R. cbn [length] in R. lia.
  - subst a. lia.
Qed.

End Pure.
End M02APure.

Import M02APure.

(* ---- M02_inv across the turn's writes ---- *)

(* The store `sw s2,0x40(sp)`: 4 bytes inside main's cell r, [S - 144, S - 126) of M02_W, below 2^47. *)
Lemma ma_inv_sw : forall S m0 m a (v : word), M02_inv S m0 m -> store_ok rsegs m (wa a) 4 = true ->
  S - 208 + 64 <= a -> a + 4 <= S - 208 + 82 -> 0x60000 <= S - 65536 -> S <= 2 ^ 47 ->
  M02_inv S m0 (write_to_mem m (wa a) (le4 v)).
Proof.
  intros S m0 m a v (MU & WM & MI & TM) HS H1 H2 HT H47.
  split.
  { apply munch_write; [exact MU | lia | rewrite length_le4; lia |].
    rewrite length_le4. unfold M02_W, M02_FRAME. cbn [inside]. right. left. lia. }
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | rewrite length_le4; exact HS]|].
  intros x b E. rewrite write_to_mem_spec in E by (rewrite ?length_le4; lia).
  destruct (Z.leb a (bv_unsigned x) && Z.ltb (bv_unsigned x) (a + Z.of_nat (length (le4 v))))%bool eqn:R.
  - right. apply andb_true_iff in R as [_ R]. apply Z.ltb_lt in R. rewrite length_le4 in R.
    rewrite m02_TASK_SIZE. lia.
  - exact (TM x b E).
Qed.

(* reac_segconf_role's post: its frames and, when it answers Some, the out cell sp + 0x40. *)
Lemma ma_inv_role : forall S m0 m m' o (wsp wout : word),
  munch (role_W (bv_unsigned wsp) (bv_unsigned wout) o) m m' -> M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wout = Z_to_bv 64 (S - 208 + 64) ->
  wmono rsegs m m' -> mem_inv rsegs m' -> 0x60000 <= S - 65536 -> S <= 2 ^ 47 -> M02_inv S m0 m'.
Proof.
  intros S m0 m m' o wsp wout MU HI -> -> WM MI HT H47.
  rewrite !unsigned_lit in MU by lia.
  assert (E0 : (S - 208 + 64 =? 0) = false) by (apply Z.eqb_neq; lia).
  apply (m02_inv_step S m0 m m' _ HI MU WM MI).
  - intros x Hx. unfold M02_W, M02_FRAME in Hx. cbn [outside] in Hx. destruct Hx as (X1 & X2 & _).
    unfold role_W, ROLE_STACK, FIND_STACK. destruct o as [v|]; [rewrite E0|]; cbn [outside]; repeat split; lia.
  - intros x Rx O. unfold role_W, ROLE_STACK, FIND_STACK in O. apply Z.nle_gt. intros C. apply O.
    destruct o as [v|]; [rewrite E0|]; cbn [outside]; repeat split; lia.
Qed.

(* The cell r after reac_segconf_role: the role it stored, or still 0x5a. *)
Lemma ma_role_cell : forall S m1 m2 o (wsp wout : word),
  munch (role_W (bv_unsigned wsp) (bv_unsigned wout) o) m1 m2 ->
  (match o with
   | Some v => bv_unsigned wout <> 0 -> bytes_at rsegs m2 (bv_unsigned wout) (le4 (Z_to_bv 64 v))
   | None => True
   end) ->
  wsp = Z_to_bv 64 (S - 208) -> wout = Z_to_bv 64 (S - 208 + 64) ->
  bytes_at rsegs m1 (S - 208 + 64) (le4 (Z_to_bv 64 90)) -> 0x60000 <= S - 65536 -> S <= 2 ^ 47 ->
  bytes_at rsegs m2 (S - 208 + 64) (le4 (Z_to_bv 64 (match o with Some v => v | None => 90 end))).
Proof.
  intros S m1 m2 o wsp wout MU Q -> -> HC HT H47.
  rewrite !unsigned_lit in MU by lia.
  destruct o as [v|]; cbv beta iota in Q |- *.
  - rewrite unsigned_lit in Q by lia. apply Q. lia.
  - eapply bytes_at_transport; [exact HC | exact MU |].
    rewrite length_le4. unfold role_W, ROLE_STACK, FIND_STACK.
    cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]. split; [lia | exact I].
Qed.

(* ---- One turn ---- *)

(** The state at the latch 0x13b78 after turn i: s1 = i, s2 = 0x5a, s3 = m + 256 i, the saved registers as at the
    turn's start, the memory an M02_inv successor of m0. *)
Definition m02_latch (S c mm : Z) (i : nat) (gp tp s5 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' t3' t4' t5' t6' : word)
                   (m' : word -> option byte),
    ms = MS (mkR ra' (Z_to_bv 64 (S - M02_FRAME)) gp tp t0' t1' t2' (Z_to_bv 64 mm) (Z_to_bv 64 (Z.of_nat i))
                 a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 90) (Z_to_bv 64 (mm + 256 * Z.of_nat i)) s4' s5 s6 s7
                 (Z_to_bv 64 c) s9 (Z_to_bv 64 (mm + MC_N)) s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x13b78) fc None m' (seg_rom rsegs) /\
    M02_inv S m0 m'.

Section T.
Variables (S c mm cap : Z) (rc : rconf) (mc : mconf) (m0 : word -> option byte) (i : nat).
Hypothesis HM : M02_mem S c mm cap rc mc m0.
Hypothesis Hi : (i < length (mc_seg mc))%nat.
Hypothesis CK : check_seg rc (nth i (mc_seg mc) mseg_d) = true.
Hypotheses (HRo : reac_segconf_role_contract) (HCR : check_role_contract) (HMo : reac_segconf_model_contract)
  (HCM : check_model_contract) (HIg : reac_segconf_ignored_contract) (HCI : check_ignore_contract)
  (HRF : reac_segconf_role_file_contract) (HIF : reac_segconf_ignore_file_contract)
  (HCP : check_provenance_contract).

Local Abbreviation Gi := (nth i (mc_seg mc) mseg_d).
Local Abbreviation NMi := (ms_name (nth i (mc_seg mc) mseg_d)).

Lemma ma_bnds : S mod 16 = 0 /\ 0x60000 <= S - 65536 /\ S <= 2 ^ 47 /\
  0 < c /\ c mod 16 = 0 /\ c + 16616 <= S - 65536 /\ 0 < mm /\ mm mod 16 = 0 /\ mm + 9236 <= S - 65536.
Proof.
  destruct HM as (_ & _ & _ & H16 & HT & H47 & _ & _ & _ & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm & _).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm. repeat split; assumption.
Qed.

Lemma ma_i32 : (i < 32)%nat.
Proof.
  destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bs & _ & (_ & L32 & _))).
  lia.
Qed.

(* The stack region of a callee of main. *)
Lemma ma_stk : forall m d, M02_inv S m0 m -> 0 <= d <= 65536 - 208 -> stack_ok rsegs m (S - 65536) (S - 208) d.
Proof. intros m d HI Hd. eapply m02_stack_ok; try eassumption; unfold M02_FRAME; lia. Qed.

(* The reader queries' premise: c holding rc, the name of m->seg[i] at m + 256 i. *)
Lemma ma_qpre : forall m depth (wsp wc wn : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wc = Z_to_bv 64 c -> wn = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  0 <= depth <= 65536 - 208 ->
  query_pre depth m (bv_unsigned wsp) (S - 65536) (bv_unsigned wc) (bv_unsigned wn) rc NMi.
Proof.
  intros m depth wsp wc wn HI -> -> -> Hd.
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm). pose proof ma_i32 as Hi32.
  rewrite !unsigned_lit by lia.
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mname rsegs m mm mc i MC Hm16 Hi) as (NZ & _ & _ & _ & NL).
  unfold query_pre, apart, SEG_C_SIZE.
  split; [lia|]. split; [exact Hc16|]. split; [eapply m02_rconf; eassumption|]. split; [left; lia|].
  split; [lia|]. split; [exact NZ|]. split; [left; lia|].
  split; [apply ma_stk; assumption | eapply m02_mem_inv; eassumption].
Qed.

Lemma ma_role_pre : forall m (wsp wc wn wout : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wc = Z_to_bv 64 c -> wn = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  wout = Z_to_bv 64 (S - 208 + 64) ->
  role_pre m (bv_unsigned wsp) (S - 65536) (bv_unsigned wc) (bv_unsigned wn) (bv_unsigned wout) rc NMi.
Proof.
  intros m wsp wc wn wout HI Esp Ec En Eo.
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold role_pre. split.
  { apply ma_qpre; [exact HI | exact Esp | exact Ec | exact En | unfold ROLE_STACK, FIND_STACK; lia]. }
  right. subst wsp wout. rewrite !unsigned_lit by lia.
  split; [Z.div_mod_to_equations; lia|].
  split; [eapply ma_wr; [eapply m02_stk; eassumption | lia | lia | lia] | unfold apart; right; lia].
Qed.

(* The entry g = m->seg[i] a check reads. *)
Lemma ma_gpre : forall m (wsp wg : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wg = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  bv_unsigned wg mod 4 = 0 /\ mseg_at rsegs m (bv_unsigned wg) Gi /\
  apart (bv_unsigned wg) MSEG_SIZE (S - 65536) (bv_unsigned wsp).
Proof.
  intros m wsp wg HI -> ->.
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm). pose proof ma_i32 as Hi32.
  rewrite !unsigned_lit by lia.
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  split; [Z.div_mod_to_equations; lia|].
  split; [exact (mb_mseg_at rsegs m mm mc i MC Hi)|].
  unfold apart, MSEG_SIZE. left. lia.
Qed.

Lemma ma_crole_pre : forall m o (wsp wset wgot wg : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wset = Z_to_bv 64 (match o with Some _ => 1 | None => 0 end) ->
  wgot = Z_to_bv 64 (match o with Some v => v | None => 90 end) -> wg = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  0 <= (match o with Some v => v | None => 90 end) < 2 ^ 31 ->
  (match o with
   | Some r => ms_role_set Gi && (r =? ms_role Gi)
   | None => negb (ms_role_set Gi)
   end) = true ->
  check_role_pre m (bv_unsigned wsp) (S - 65536) (bv_unsigned wset) (bv_unsigned wgot) (bv_unsigned wg) o Gi.
Proof.
  intros m o wsp wset wgot wg HI Esp Eset Egot Eg Hw CR.
  destruct (ma_gpre m wsp wg HI Esp Eg) as (G1 & G2 & G3).
  pose proof ma_bnds as (H16 & HT & H47 & _).
  unfold check_role_pre.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  subst wset wgot.
  split; [destruct o; reflexivity|].
  split; [destruct o as [v|]; cbv beta iota in Hw |- *; [rewrite unsigned_lit by lia; split; lia | exact I]|].
  split; [exact CR|].
  split; [subst wsp; rewrite unsigned_lit by lia; apply ma_stk; [exact HI | unfold CHECK_ROLE_STACK; lia]|].
  eapply m02_mem_inv; eassumption.
Qed.

Lemma ma_cmodel_pre : forall m (wsp wgot wg : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wgot = Z_to_bv 64 (model_ptr c rc NMi) ->
  wg = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  same_text (r_model rc NMi) (if ms_model_set Gi then Some (ms_model Gi) else None) = true ->
  check_model_pre m (bv_unsigned wsp) (S - 65536) (bv_unsigned wgot) (bv_unsigned wg) (r_model rc NMi) Gi.
Proof.
  intros m wsp wgot wg HI Esp Egot Eg CM.
  destruct (ma_gpre m wsp wg HI Esp Eg) as (G1 & G2 & G3).
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & _).
  assert (RC : rconf_at rsegs m c rc) by (eapply m02_rconf; eassumption).
  destruct (mb_model rsegs m c rc NMi RC ltac:(lia)) as [OZ OB].
  pose proof (ma_ocz_rng _ _ _ _ OZ) as R.
  subst wgot. rewrite (unsigned_lit (model_ptr c rc NMi)) by lia.
  unfold check_model_pre.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact OZ|].
  split.
  { destruct (r_model rc NMi) as [s|] eqn:E; [|exact I].
    pose proof (OB s ltac:(first [exact E | reflexivity])) as B. unfold SEG_C_SIZE in B. unfold apart. left. lia. }
  split; [exact CM|].
  split; [subst wsp; rewrite unsigned_lit by lia; apply ma_stk; [exact HI | unfold CHECK_MODEL_STACK; lia]|].
  eapply m02_mem_inv; eassumption.
Qed.

Lemma ma_cign_pre : forall m (wsp wgot wg : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wgot = Z_to_bv 64 (b2z (r_ignored rc NMi)) ->
  wg = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  Bool.eqb (r_ignored rc NMi) (ms_ignore Gi) = true ->
  check_ignore_pre m (bv_unsigned wsp) (S - 65536) (bv_unsigned wgot) (bv_unsigned wg) (r_ignored rc NMi) Gi.
Proof.
  intros m wsp wgot wg HI Esp Egot Eg CI.
  destruct (ma_gpre m wsp wg HI Esp Eg) as (G1 & G2 & G3).
  pose proof ma_bnds as (H16 & HT & H47 & _).
  unfold check_ignore_pre.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
  split; [subst wgot; unfold b2z; destruct (r_ignored rc NMi); reflexivity|].
  split; [exact CI|].
  split; [subst wsp; rewrite unsigned_lit by lia; apply ma_stk; [exact HI | unfold CHECK_IGNORE_STACK; lia]|].
  eapply m02_mem_inv; eassumption.
Qed.

Lemma ma_cprov_pre : forall m (wsp wrf wif wg : word), M02_inv S m0 m ->
  wsp = Z_to_bv 64 (S - 208) -> wrf = Z_to_bv 64 (role_file_ptr c rc NMi) ->
  wif = Z_to_bv 64 (ignore_file_ptr c rc NMi) -> wg = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  same_text (r_role_file rc NMi) (if ms_role_set Gi then Some (ms_role_file Gi) else None) = true ->
  same_text (r_ignore_file rc NMi) (if ms_ignore_set Gi then Some (ms_ignore_file Gi) else None) = true ->
  check_provenance_pre m (bv_unsigned wsp) (S - 65536) (bv_unsigned wrf) (bv_unsigned wif) (bv_unsigned wg)
    (r_role_file rc NMi) (r_ignore_file rc NMi) Gi.
Proof.
  intros m wsp wrf wif wg HI Esp Erf Eif Eg C1 C2.
  destruct (ma_gpre m wsp wg HI Esp Eg) as (G1 & G2 & G3).
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & _).
  assert (RC : rconf_at rsegs m c rc) by (eapply m02_rconf; eassumption).
  destruct (mb_role_file rsegs m c rc NMi RC ltac:(lia)) as [OR BR].
  destruct (mb_ignore_file rsegs m c rc NMi RC ltac:(lia)) as [OI BI].
  pose proof (ma_ocz_rng _ _ _ _ OR) as RR. pose proof (ma_ocz_rng _ _ _ _ OI) as RI.
  subst wrf wif.
  rewrite (unsigned_lit (role_file_ptr c rc NMi)) by lia. rewrite (unsigned_lit (ignore_file_ptr c rc NMi)) by lia.
  unfold check_provenance_pre.
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact OR|].
  split.
  { destruct (r_role_file rc NMi) as [s|] eqn:E; [|exact I].
    pose proof (BR s ltac:(first [exact E | reflexivity])) as B. unfold SEG_C_SIZE in B. unfold apart. left. lia. }
  split; [exact OI|].
  split.
  { destruct (r_ignore_file rc NMi) as [s|] eqn:E; [|exact I].
    pose proof (BI s ltac:(first [exact E | reflexivity])) as B. unfold SEG_C_SIZE in B. unfold apart. left. lia. }
  split; [exact C1|]. split; [exact C2|].
  split; [subst wsp; rewrite unsigned_lit by lia; apply ma_stk; [exact HI | unfold CHECK_PROVENANCE_STACK; lia]|].
  eapply m02_mem_inv; eassumption.
Qed.

Lemma ma_turn : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  M02_inv S m0 m ->
  evt rsegs (m02_latch S c mm i gp tp s5 s6 s7 s9 s11 F fc m0)
    (MS (mkR ra (Z_to_bv 64 (S - M02_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 mm) (Z_to_bv 64 (Z.of_nat i))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 90) (Z_to_bv 64 (mm + 256 * Z.of_nat i)) s4 s5 s6 s7
             (Z_to_bv 64 c) s9 (Z_to_bv 64 (mm + MC_N)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b04) fc None m (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 gp tp F fc m HI.
  pose proof ma_bnds as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm). pose proof ma_i32 as Hi32.
  pose proof CK as CK0. unfold check_seg in CK0. cbv zeta in CK0.
  apply andb_true_iff in CK0 as [CK0 CIF]. apply andb_true_iff in CK0 as [CK0 CRF].
  apply andb_true_iff in CK0 as [CK0 CIG]. apply andb_true_iff in CK0 as [CRO CMO].
  unfold M02_FRAME.
  lazymatch goal with |- evt _ ?Q _ => set (Post := Q) end.
  (* 0x13b04 sw s2,0x40(sp): main's cell r = 0x5a *)
  assert (HW0 : wr_at rsegs m (S - 208 + 64) 4)
    by (eapply ma_wr; [eapply m02_stk; eassumption | lia | lia | lia]).
  pose proof (wr_at_store_ok rsegs m (S - 208 + 64) 4 0 4 HW0 ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS.
  step.
  change (Z_to_bv 64 (S - 208 + 64)) with (wa (S - 208 + 64)).
  assert (HI1 : M02_inv S m0 (write_to_mem m (wa (S - 208 + 64)) (le4 (Z_to_bv 64 90))))
    by (apply ma_inv_sw; [exact HI | exact HS | lia | lia | lia | lia]).
  assert (HC1 : bytes_at rsegs (write_to_mem m (wa (S - 208 + 64)) (le4 (Z_to_bv 64 90))) (S - 208 + 64)
                  (le4 (Z_to_bv 64 90)))
    by (apply bytes_at_write_same; rewrite ?length_le4; lia).
  set (m1 := write_to_mem m (wa (S - 208 + 64)) (le4 (Z_to_bv 64 90))) in *. clearbody m1. clear HI HS HW0.
  (* 0x13b08 addi a2,sp,0x40; mv a0,s8; mv a1,s3; jal reac_segconf_role *)
  do 4 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HRo with (lo := S - 65536) (rc := rc) (nm := NMi).
    eapply ma_role_pre; first [exact HI1 | word_eq_tac]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m2 & -> & MU2 & WM2 & MI2 & _ & Q2).
  assert (HI2 : M02_inv S m0 m2)
    by (eapply ma_inv_role; [exact MU2 | exact HI1 | word_eq_tac | word_eq_tac | exact WM2 | exact MI2 | lia | lia]).
  assert (HC2 : bytes_at rsegs m2 (S - 208 + 64)
                  (le4 (Z_to_bv 64 (match r_role rc NMi with Some v => v | None => 90 end))))
    by (eapply ma_role_cell; [exact MU2 | exact Q2 | word_eq_tac | word_eq_tac | exact HC1 | lia | lia]).
  assert (Hw : 0 <= (match r_role rc NMi with Some v => v | None => 90 end) < 2 ^ 31).
  { destruct (r_role rc NMi) as [v|] eqn:E; cbv beta iota; [|lia].
    eapply mb_role_rng; [eapply m02_rconf; eassumption | exact E]. }
  clear MU2 WM2 Q2 HC1 HI1.
  set (o := r_role rc NMi) in *. clearbody o.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b18 lw a1,0x40(sp) *)
  pose proof (m02_rd4 rsegs m2 _ _ HC2) as RD.
  zstep. clear RD.
  rewrite (sx32_small (match o with Some v => v | None => 90 end)) by lia.
  (* 0x13b1c mv a2,s3; jal check_role *)
  do 2 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HCR with (lo := S - 65536) (o := o) (g := Gi).
    eapply ma_crole_pre; first [exact HI2 | exact Hw | exact CRO | word_eq_tac]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3 & -> & MU3 & WM3 & MI3 & _ & _).
  pose proof (m02_inv_nil S m0 m2 m3 MU3 HI2 WM3 MI3) as HI3.
  clear MU3 WM3 HC2 HI2.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b24 mv a0,s8; mv a1,s3; jal reac_segconf_model *)
  do 3 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HMo with (lo := S - 65536) (rc := rc) (nm := NMi).
    eapply ma_qpre; first [exact HI3 | word_eq_tac | unfold MODEL_STACK, FIND_STACK; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & _ & _).
  assert (HI4 : M02_inv S m0 m4)
    by (eapply m02_inv_call; [exact MU4 | exact HI3 | word_eq_tac | exact WM4 | exact MI4
                            | unfold MODEL_STACK, FIND_STACK; lia | lia | lia]).
  clear MU4 WM4 HI3.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit c) by lia.
  (* 0x13b30 mv a1,s3; jal check_model *)
  do 2 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HCM with (lo := S - 65536) (o := r_model rc NMi) (g := Gi).
    eapply ma_cmodel_pre; first [exact HI4 | exact CMO | word_eq_tac]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m5 & -> & MU5 & WM5 & MI5 & _ & _).
  assert (HI5 : M02_inv S m0 m5)
    by (eapply m02_inv_call; [exact MU5 | exact HI4 | word_eq_tac | exact WM5 | exact MI5
                            | unfold CHECK_MODEL_STACK; lia | lia | lia]).
  clear MU5 WM5 HI4.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b38 mv a0,s8; mv a1,s3; jal reac_segconf_ignored *)
  do 3 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HIg with (lo := S - 65536) (rc := rc) (nm := NMi).
    eapply ma_qpre; first [exact HI5 | word_eq_tac | unfold IGNORED_STACK, FIND_STACK; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU6 & WM6 & MI6 & _ & _).
  assert (HI6 : M02_inv S m0 m6)
    by (eapply m02_inv_call; [exact MU6 | exact HI5 | word_eq_tac | exact WM6 | exact MI6
                            | unfold IGNORED_STACK, FIND_STACK; lia | lia | lia]).
  clear MU6 WM6 HI5.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b44 mv a1,s3; jal check_ignore *)
  do 2 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HCI with (lo := S - 65536) (b := r_ignored rc NMi) (g := Gi).
    eapply ma_cign_pre; first [exact HI6 | exact CIG | word_eq_tac]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & _ & _).
  pose proof (m02_inv_nil S m0 m6 m7 MU7 HI6 WM7 MI7) as HI7.
  clear MU7 WM7 HI6.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b4c mv a0,s8; mv a1,s3; jal reac_segconf_role_file *)
  do 3 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HRF with (lo := S - 65536) (rc := rc) (nm := NMi).
    eapply ma_qpre; first [exact HI7 | word_eq_tac | unfold ROLE_FILE_STACK, FIND_STACK; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m8 & -> & MU8 & WM8 & MI8 & _ & _).
  assert (HI8 : M02_inv S m0 m8)
    by (eapply m02_inv_call; [exact MU8 | exact HI7 | word_eq_tac | exact WM8 | exact MI8
                            | unfold ROLE_FILE_STACK, FIND_STACK; lia | lia | lia]).
  clear MU8 WM8 HI7.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit c) by lia.
  (* 0x13b58 mv s4,a0; mv a0,s8; mv a1,s3; jal reac_segconf_ignore_file *)
  do 4 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HIF with (lo := S - 65536) (rc := rc) (nm := NMi).
    eapply ma_qpre; first [exact HI8 | word_eq_tac | unfold IGNORE_FILE_STACK, FIND_STACK; lia]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m9 & -> & MU9 & WM9 & MI9 & _ & _).
  assert (HI9 : M02_inv S m0 m9)
    by (eapply m02_inv_call; [exact MU9 | exact HI8 | word_eq_tac | exact WM9 | exact MI9
                            | unfold IGNORE_FILE_STACK, FIND_STACK; lia | lia | lia]).
  clear MU9 WM9 HI8.
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite (unsigned_lit c) by lia.
  (* 0x13b68 mv a1,a0; mv a0,s4; mv a2,s3; jal check_provenance *)
  do 4 zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
  eapply evt_cut.
  { eapply HCP with (lo := S - 65536) (orf := r_role_file rc NMi) (oif := r_ignore_file rc NMi) (g := Gi).
    eapply ma_cprov_pre; first [exact HI9 | exact CRF | exact CIF | word_eq_tac]. }
  intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m10 & -> & MU10 & WM10 & MI10 & _ & _).
  assert (HI10 : M02_inv S m0 m10)
    by (eapply m02_inv_call; [exact MU10 | exact HI9 | word_eq_tac | exact WM10 | exact MI10
                            | unfold CHECK_PROVENANCE_STACK; lia | lia | lia]).
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13b78: the latch *)
  apply evt_done. unfold Post, m02_latch.
  do 18 eexists. split; [reflexivity | exact HI10].
Qed.

End T.

(** Turn i of piece A's loop, from 0x13b04 to the latch 0x13b78. *)
Lemma m02_turn : reac_segconf_role_contract -> check_role_contract -> reac_segconf_model_contract ->
  check_model_contract -> reac_segconf_ignored_contract -> check_ignore_contract ->
  reac_segconf_role_file_contract -> reac_segconf_ignore_file_contract -> check_provenance_contract ->
  forall (S c mm cap : Z) (rc : rconf) (mc : mconf) (m0 : word -> option byte) (i : nat),
  M02_mem S c mm cap rc mc m0 -> (i < length (mc_seg mc))%nat -> check_seg rc (nth i (mc_seg mc) mseg_d) = true ->
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 gp tp : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  M02_inv S m0 m ->
  evt rsegs (m02_latch S c mm i gp tp s5 s6 s7 s9 s11 F fc m0)
    (MS (mkR ra (Z_to_bv 64 (S - M02_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 mm) (Z_to_bv 64 (Z.of_nat i))
             a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 90) (Z_to_bv 64 (mm + 256 * Z.of_nat i)) s4 s5 s6 s7
             (Z_to_bv 64 c) s9 (Z_to_bv 64 (mm + MC_N)) s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13b04) fc None m (seg_rom rsegs)).
Proof.
  intros HRo HCR HMo HCM HIg HCI HRF HIF HCP S c mm cap rc mc m0 i HM Hi CK
    ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 gp tp F fc m HI.
  eapply ma_turn; eassumption.
Qed.
