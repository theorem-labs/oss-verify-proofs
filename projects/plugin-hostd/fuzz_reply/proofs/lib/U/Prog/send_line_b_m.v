From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO0x YO10 YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c __errno_location_c send_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_b_c KindB send_line_loop
  send_line_seg send_line_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sb_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma sb_munch_cat : forall W1 W2 (m m1 m2 : word -> option byte),
  munch W1 m m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 H1 H2 x Hx.
  assert (O1 : outside W1 (bv_unsigned x) /\ outside W2 (bv_unsigned x)).
  { clear H1 H2. induction W1 as [|[lo hi] W1 IH]; cbn [app outside] in *; [split; [exact I | exact Hx]|].
    destruct Hx as [Hx1 Hx2]. destruct (IH Hx2) as [P Q]. split; [split; [exact Hx1 | exact P] | exact Q]. }
  destruct O1 as [O1 O2]. rewrite (H2 x O2). exact (H1 x O1).
Qed.

Lemma sb_outside_dec : forall W a, outside W a \/ exists lo hi, In (lo, hi) W /\ lo <= a < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn [outside]; [left; exact I|].
  destruct (Z_le_gt_dec lo a); destruct (Z_lt_ge_dec a hi).
  - right. exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH a) as [H|(x1 & y1 & Hin & Hl)]; [left; split; [lia | exact H] | right; exists x1, y1; split; [right; exact Hin | exact Hl]].
  - destruct (IH a) as [H|(x1 & y1 & Hin & Hl)]; [left; split; [lia | exact H] | right; exists x1, y1; split; [right; exact Hin | exact Hl]].
  - destruct (IH a) as [H|(x1 & y1 & Hin & Hl)]; [left; split; [lia | exact H] | right; exists x1, y1; split; [right; exact Hin | exact Hl]].
Qed.

Section SB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Hypothesis BW : blocks_writable Bm API.
Hypothesis EU : errno_unowned Bm API.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTXO : ctx_owned Bm API.

Lemma sb_rp_regs : forall K E F L A regs mem md L' A' mem' md' regs',
  relay_post Bm API K E F L A regs mem md L' A' regs mem' md' -> regs_preserved regs regs' ->
  relay_post Bm API K E F L A regs mem md L' A' regs' mem' md'.
Proof using.
  intros K E F L A regs mem md L' A' mem' md' regs' P RP.
  destruct P as (M1 & W1 & B1 & LL1 & LN1 & AD1 & SV1 & Z1 & OW1 & _ & MD1 & FR1 & BY1 & SC1).
  exact (conj M1 (conj W1 (conj B1 (conj LL1 (conj LN1 (conj AD1 (conj SV1 (conj Z1 (conj OW1 (conj RP
    (conj MD1 (conj FR1 (conj BY1 SC1))))))))))))).
Qed.

Lemma sb_getr : forall R r, YK11.getr R r = getr R r.
Proof using. reflexivity. Qed.

Lemma sb_pres : forall regs R t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  Regs6ss.xregs_eqv (mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) t0 t1 t2
    (reg_get regs 8) (reg_get regs 9) a0 a1 a2 a3 a4 a5 a6 a7 (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
    (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25) (reg_get regs 26)
    (reg_get regs 27) t3 t4 t5 t6) R -> regs_preserved regs R.
Proof using.
  intros regs R t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 X r Hr. unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]]];
    rewrite (getr_of_eqv _ _ _ X) by reflexivity; simp_regs; reflexivity.
Qed.

Lemma sb_nrw : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs -> 0x21624 <= A ->
  rw_cells rsegs (normalize rsegs m) A cs.
Proof using.
  intros m A cs RO H HA. pose proof (rw_cells_bound rsegs m A cs H) as BA.
  apply sb_rw_norm; [exact RO | exact H |]. intros i Hi. apply sb_ro_ge. lia.
Qed.

Set Default Proof Using "All".

Section Main.
Variable RF : ResFormT.
Hypothesis MC : memcpy_contract.
Hypothesis EL : __errno_location_contract.
Hypothesis RA : realloc_contract_rt Bm API RF 0x178f8.
Hypothesis RN : realloc_null_contract_rt Bm API RF 0x178f8.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (bnd : rt_R RF)
  (Bl O junk : list byte) (cl br dd ei : Z) (mx nout cap out ev : word).
Local Abbreviation SP := (bv_unsigned (getr regs 2)).
Local Abbreviation LINE := (bv_unsigned (getr regs 10)).
Local Abbreviation LEN := (bv_unsigned (getr regs 11)).
Local Abbreviation ERR := (errno_addr Bm).
Local Abbreviation NO := (bv_unsigned nout).
Local Abbreviation CAP := (bv_unsigned cap).
Local Abbreviation OUT := (bv_unsigned out).
Local Abbreviation live := (send_live cl br dd LEN).
Local Abbreviation off := (send_off cl br LEN).
Local Abbreviation EE := (send_writes live OUT CAP).
Local Abbreviation FF := (fun q => live = true /\ q = OUT).
Local Abbreviation o0 := (known_at L A (bv_unsigned out)).
Local Abbreviation TR := (send_line_tr (send_live cl br dd (bv_unsigned (getr regs 11))) (bv_unsigned mx)
  (bv_unsigned nout) (bv_unsigned cap) (bv_unsigned (getr regs 11)) 0 (known_at L A (bv_unsigned out))).
Hypothesis H01 : ms_segs Bm = rsegs.
Hypothesis H02 : call_pre_k Bm (aa_MR API) SEND_LINE_K L A regs mem md.
Hypothesis H03 : st_init_done A = true.
Hypothesis H04 : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis H04a : ERR mod 4 = 0.
Hypothesis H05 : G_RELAY_HI <= ERR.
Hypothesis H06 : ro_agree (ms_segs Bm) mem.
Hypothesis H07 : bytes_at (ms_segs Bm) mem LINE Bl.
Hypothesis H08 : Z.of_nat (length Bl) = LEN.
Hypothesis H09 : LINE + LEN <= G_RELAY_LO \/ G_RELAY_HI <= LINE.
Hypothesis H10 : LINE + LEN <= ERR \/ ERR + 4 <= LINE.
Hypothesis H11 : LINE + LEN <= SP - SEND_LINE_K \/ SP <= LINE.
Hypothesis H12 : forall a, G_RELAY_LO <= a < G_RELAY_HI -> img_plain Bm a.
Hypothesis H13 : forall a, G_CLIENT <= a < G_CLIENT + 4 -> img_plain Bm a.
Hypothesis H14 : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis H15 : (forall a, LINE <= a < LINE + LEN -> img_plain Bm a) \/
  (exists q k, In (q, k) (blocks L A) /\ q <= LINE /\ LINE + LEN <= q + k /\ q <> OUT).
Hypothesis H16 : cl = 3 \/ cl = -1.
Hypothesis H17 : br = 0 \/ br = 1.
Hypothesis H18 : dd = 0 \/ dd = 1.
Hypothesis H19 : ei = 0 \/ ei = 1.
Hypothesis H20 : rw_cells (ms_segs Bm) mem G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis H21 : rw_cells (ms_segs Bm) mem G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis H22 : rw_cells (ms_segs Bm) mem G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis H23 : rw_cells (ms_segs Bm) mem G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis H24 : rw_cells (ms_segs Bm) mem G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis H25 : rw_cells (ms_segs Bm) mem ERR [C4 ev].
Hypothesis H26 : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L A) /\ fresh_block Bm OUT CAP /\
   bytes_at (ms_segs Bm) mem OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO /\
   (LINE + LEN <= OUT \/ OUT + CAP <= LINE)).
Hypothesis H27 : 2 * (NO + LEN) < 2 ^ 63.
Hypothesis H28 : rt_ok RF A bnd.
Hypothesis H29 : forall qs, length qs = nretF TR -> roomF RF qs bnd TR.

Definition sb_post (c' : config) : Prop :=
  exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' : list byte),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom (ms_segs Bm))) md' /\
    relay_post Bm API SEND_LINE_K EE FF L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF TR /\ rt_ok RF A' (runF RF qs bnd TR) /\
       (live = true -> live_at L' A' (resolveF qs (send_line_out live (bv_unsigned mx) NO CAP LEN 0 o0)) OUT' CAP')) /\
    ro_agree (ms_segs Bm) mem' /\
    bytes_at (ms_segs Bm) mem' LINE Bl /\
    rw_cells (ms_segs Bm) mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
    rw_cells (ms_segs Bm) mem' G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
    rw_cells (ms_segs Bm) mem' G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells (ms_segs Bm) mem' G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
    (live = false ->
       blocks L' A' = blocks L A /\
       rw_cells (ms_segs Bm) mem' ERR [C4 (if off then ev
               else if dd =? 1 then Z_to_bv 64 EPIPE_V
               else if ei =? 1 then Z_to_bv 64 EINTR_V
               else ev)] /\
       rw_cells (ms_segs Bm) mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
    (live = true ->
       NO + LEN <= CAP' /\ CAP' = send_line_cap live (bv_unsigned mx) NO CAP LEN /\
       fresh_block Bm OUT' CAP' /\ (exists ev'', rw_cells (ms_segs Bm) mem' ERR [C4 ev'']) /\
       (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> OUT') /\
       (exists b1 b2 c1 c2, blocks L' A' = c1 ++ (OUT', CAP') :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
          ((CAP = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAP /\ blocks L A = b1 ++ (OUT, CAP) :: b2))) /\
       bytes_at (ms_segs Bm) mem' OUT' (O ++ Bl ++ junk') /\ Z.of_nat (length junk') = CAP' - NO - LEN /\
       rw_cells (ms_segs Bm) mem' G_OUTV
         [C8 mx; C8 (Z_to_bv 64 (NO + LEN)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]).

Definition sb_blk (j : nat) (L1 : layout) (A1 : astate) (cap1 out1 : word) : Prop :=
  (j = 0%nat /\ L1 = L /\ A1 = A /\ cap1 = cap /\ out1 = out) \/
  ((0 < j)%nat /\ 0 < bv_unsigned cap1 /\ NO <= bv_unsigned cap1 /\ bv_unsigned cap1 <= 2 * (NO + LEN) /\
   fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
   (exists b1 b2 c1 c2, blocks L1 A1 = c1 ++ (bv_unsigned out1, bv_unsigned cap1) :: c2 /\ c1 ++ c2 = b1 ++ b2 /\
      ((CAP = 0 /\ blocks L A = b1 ++ b2) \/ (0 < CAP /\ blocks L A = b1 ++ (OUT, CAP) :: b2))) /\
   (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> bv_unsigned out1)).

(* The requests made so far (tp, their returned addresses qp, j of them), and what the rest of the run requests from
   k bytes sent with capacity c and the buffer at o (the live block at out1): together the whole trace of
   send_line. *)
Definition sb_res (L1 : layout) (A1 : astate) (out1 k c : Z) : Prop :=
  exists (tp : trF) (qp : list sptr) (j : nat) (o : adrF),
    length qp = j /\ nretF tp = j /\ wf_from sptr 0 tp /\ p3a_ok o j /\
    rt_ok RF A1 (runF RF qp bnd tp) /\
    tp ++ fst (sl_rest (bv_unsigned mx) LEN NO k c j o) = TR /\
    fst (snd (sl_rest (bv_unsigned mx) LEN NO k c j o)) = send_line_cap live (bv_unsigned mx) NO CAP LEN /\
    snd (snd (sl_rest (bv_unsigned mx) LEN NO k c j o)) = send_line_out live (bv_unsigned mx) NO CAP LEN 0 o0 /\
    (0 < c -> live_at L1 A1 (resolveF qp o) out1 c).

Lemma sb_tp : bv_unsigned (getr regs 4) = ERR + 164 /\ 203000 <= ERR /\ ERR + 4 <= 2 ^ 21.
Proof using All.
  pose proof H02 as (_ & _ & _ & _ & _ & _ & _ & _ & HTP & _).
  pose proof H04 as E4. pose proof H05 as E5. unfold ERRNO_OFF, G_RELAY_HI in E4, E5.
  pose proof (in_img_low Bm H01 _ (H14 ERR ltac:(lia))) as I0.
  pose proof (in_img_low Bm H01 _ (H14 (ERR + 3) ltac:(lia))) as I3.
  rewrite sb_getr in HTP. rewrite HTP. rewrite unsigned_lit by lia. lia.
Qed.

Lemma sb_sp : YM05.alloc_ceiling + 8368 <= SP /\ SP < 2 ^ 63 /\ SP mod 16 = 0 /\ 2 ^ 46 <= YM05.alloc_ceiling.
Proof using All.
  pose proof H02 as (_ & _ & _ & _ & HAL & HC & H63 & _).
  unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK in HC.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. unfold spZ in *. rewrite !sb_getr in *. lia.
Qed.

Lemma sb_rp_refl : relay_post Bm API SEND_LINE_K EE FF L A regs mem md L A regs mem md.
Proof using All.
  pose proof H02 as (HM & HWF & HBD & _ & _ & _ & _ & HWS & _ & HWE & _).
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [apply layout_le_refl|]. split; [lia|].
  split; [intros; reflexivity|]. split; [intros p n H _ _; exact H|].
  split; [intros p H; split; [exact H | reflexivity]|].
  split; [intros a _ H; exact H|].
  split; [intros r _; reflexivity|].
  split; [exists (m_vmmaps md); symmetry; apply sb_vm_id|].
  split; [intros; split; [reflexivity | tauto]|].
  split; [intros; reflexivity|].
  intros a [Ha|Ha]; [apply HWS; exact Ha | apply HWE; exact Ha].
Qed.

Definition sb_fin_at (cap1 out1 : word) (dd0 e k : Z) (ev nk : word) (r : Z) (m1 : word -> option byte)
    (ms : machine_state) : Prop :=
  sl_fin (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 10)
    (reg_get regs 11) mx cap1 out1 fp_regs fp_csr Bl (reg_get regs 1) (reg_get regs 8) (reg_get regs 9)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (SP - 8368) dd0 e k ev nk r m1 ms.

Definition sb_call_at (cap1 out1 : word) (jb : list byte) (dd0 e k : Z) (ev nk : word) (r : Z)
    (m1 : word -> option byte) (ms : machine_state) : Prop :=
  sl_call (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 10)
    (reg_get regs 11) mx cap1 out1 fp_regs fp_csr Bl (reg_get regs 1) (reg_get regs 8) (reg_get regs 9)
    (reg_get regs 18) (reg_get regs 19) (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23)
    (reg_get regs 24) (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (SP - 8368) jb dd0 e k ev nk r m1 ms.

Lemma sb_etp : bv_unsigned (reg_get regs 4) + -164 = ERR.
Proof using All. pose proof sb_tp as (T1 & _). change (reg_get regs 4) with (getr regs 4). lia. Qed.

Lemma sb_out_img : forall Wpre (b : bool) P T a,
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  in_img Bm a -> ~ (ERR <= a < ERR + 4) -> a <> 202916 -> a <> 202928 -> ~ (202976 <= a < 203000) ->
  (forall i, 0 <= i < T -> ~ in_img Bm (P + i)) ->
  outside (Wpre ++ sl_wit (reg_get regs 4) b P T) a.
Proof using All.
  intros Wpre b P T a WPRE HI NE N1 N2 N3 HT.
  pose proof (in_img_low Bm H01 a HI) as IL. pose proof sb_sp as (S1 & S2 & S3 & S4).
  destruct (sb_outside_dec (Wpre ++ sl_wit (reg_get regs 4) b P T) a) as [Ho|(lo & hi & Hin & Hlh)]; [exact Ho|exfalso].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (WPRE lo hi Hin); lia.
  - unfold sl_wit in Hin. rewrite sb_etp in Hin. cbn [app In] in Hin.
    destruct Hin as [E|[E|[E|[E|Hin]]]]; try (injection E as <- <-; lia).
    destruct b; cbn [In] in Hin; [|destruct Hin].
    destruct Hin as [E|[]]. injection E as <- <-.
    apply (HT (a - P)); [lia|]. replace (P + (a - P)) with a by lia. exact HI.
Qed.

Lemma sb_out_blk : forall Wpre (b : bool) P T a,
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  0 <= a < YM05.alloc_ceiling -> ~ in_img Bm a -> ~ (P <= a < P + T) ->
  outside (Wpre ++ sl_wit (reg_get regs 4) b P T) a.
Proof using All.
  intros Wpre b P T a WPRE Ha NI NP. pose proof sb_sp as (S1 & S2 & S3 & S4).
  destruct (sb_outside_dec (Wpre ++ sl_wit (reg_get regs 4) b P T) a) as [Ho|(lo & hi & Hin & Hlh)]; [exact Ho|exfalso].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (WPRE lo hi Hin) as [F|F]; [lia|]. apply NI. apply H12. unfold G_RELAY_LO, G_RELAY_HI. lia.
  - unfold sl_wit in Hin. rewrite sb_etp in Hin. cbn [app In] in Hin.
    destruct Hin as [E|[E|[E|[E|Hin]]]].
    + injection E as <- <-. apply NI. apply H14. lia.
    + injection E as <- <-. apply NI. apply H12. unfold G_RELAY_LO, G_RELAY_HI. lia.
    + injection E as <- <-. apply NI. apply H12. unfold G_RELAY_LO, G_RELAY_HI. lia.
    + injection E as <- <-. apply NI. apply H12. unfold G_RELAY_LO, G_RELAY_HI. lia.
    + destruct b; cbn [In] in Hin; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-. lia.
Qed.

Lemma sb_W_ok : forall L1 A1 mem1 md1 j cap1 out1 Wpre P T,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  sb_blk j L1 A1 cap1 out1 -> off = false ->
  (live = true -> NO <= bv_unsigned cap1 /\
     (0 < bv_unsigned cap1 -> In (bv_unsigned out1, bv_unsigned cap1) (blocks L1 A1))) ->
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  (dd = 0 -> P = bv_unsigned out1 + NO /\ T = bv_unsigned cap1 - NO) ->
  forall a, 0 <= a < 2 ^ 64 -> outside (Wpre ++ sl_wit (reg_get regs 4) (dd =? 0) P T) a \/
     (SP - SEND_LINE_K <= a < SP /\ YM05.alloc_ceiling <= a) \/ (img_plain Bm a /\ EE a) \/
     (ERR <= a < ERR + 4) \/
     (~ in_img Bm a /\ (exists q k, In (q, k) (blocks L1 A1) /\ q <= a < q + k) /\
      forall p n i, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ~ FF (ptr_addr L p) -> 0 <= i < n ->
        ~ EE (ptr_addr L p + i) -> ptr_addr L p + i <> a).
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 Wpre P T RP BLK NOFF LV WPRE PT a Ha.
  pose proof sb_sp as (S1 & S2 & S3 & S4).
  destruct (sb_outside_dec (Wpre ++ sl_wit (reg_get regs 4) (dd =? 0) P T) a) as [Hout|(lo & hi & Hin & Hlh)];
    [left; exact Hout | right].
  apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (WPRE lo hi Hin) as [F|F].
    + left. unfold SEND_LINE_K, SEND_LINE_FRAME, REALLOC_STACK, ALLOC_STACK. lia.
    + right; left. split; [apply H12; unfold G_RELAY_LO, G_RELAY_HI; lia|].
      unfold send_writes, G_OUTV. right; right; left. lia.
  - unfold sl_wit in Hin. rewrite sb_etp in Hin. cbn [app In] in Hin.
    destruct Hin as [E|[E|[E|[E|Hin]]]].
    + injection E as <- <-. right; right; left. lia.
    + injection E as <- <-. right; left. split; [apply H12; unfold G_RELAY_LO, G_RELAY_HI; lia|].
      unfold send_writes, G_BROKEN. left. lia.
    + injection E as <- <-. right; left. split; [apply H12; unfold G_RELAY_LO, G_RELAY_HI; lia|].
      unfold send_writes, G_EINTR. right; left. lia.
    + injection E as <- <-. right; left. split; [apply H12; unfold G_RELAY_LO, G_RELAY_HI; lia|].
      unfold send_writes, G_OUTV. right; right; left. lia.
    + destruct (Z.eqb_spec dd 0) as [D|D]; cbn [In] in Hin; [|destruct Hin].
      destruct Hin as [E|[]]. injection E as <- <-.
      destruct (PT D) as [-> ->].
      assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D).
      destruct (LV LIVE) as [HNO HIN].
      assert (C0 : 0 < bv_unsigned cap1) by lia.
      specialize (HIN C0).
      destruct RP as (M1 & _ & _ & _ & _ & AD1 & _).
      right; right; right.
      split.
      { pose proof HIN as HIN'. unfold blocks in HIN'. apply in_map_iff in HIN' as ([p1 n1] & Eq & Hp1).
        cbn [fst snd] in Eq. injection Eq as E1 E2.
        pose proof (ax_blocks_img AX L1 A1 mem1 md1 p1 n1 (a - bv_unsigned out1) M1 Hp1 ltac:(lia)) as NI.
        rewrite E1 in NI. replace (bv_unsigned out1 + (a - bv_unsigned out1)) with a in NI by lia. exact NI. }
      split; [exists (bv_unsigned out1), (bv_unsigned cap1); split; [exact HIN | lia]|].
      intros p n i Hp Hp1 NF Hi NE Eq.
      destruct BLK as [(J0 & -> & -> & -> & ->) | (J0 & Cp & NOle & Cle & FRE & DEC & NEQ)].
      * apply NE. unfold send_writes. right; right; right. split; [exact LIVE | lia].
      * assert (NOUT : ptr_addr L p <> OUT) by (intros E; apply NF; split; [exact LIVE | exact E]).
        pose proof (AD1 p n Hp Hp1 NF) as EA.
        assert (IB : In (ptr_addr L p, n) (blocks L A))
          by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (p, n) Hp)).
        pose proof (NEQ _ _ IB NOUT ltac:(lia)) as NE1.
        assert (IB1 : In (ptr_addr L1 p, n) (blocks L1 A1))
          by (unfold blocks; exact (in_map (fun b => (ptr_addr L1 (fst b), snd b)) _ (p, n) Hp1)).
        rewrite EA in IB1.
        pose proof (blocks_disjoint Bm API L1 A1 mem1 md1 _ _ _ _ M1 IB1 HIN NE1) as DJ. lia.
Qed.

Lemma sb_lo : Z.of_nat (length O) = NO.
Proof using All. destruct H26 as [(_ & _ & N0 & ->)|(_ & _ & _ & _ & _ & LO & _)]; [cbn; lia | exact LO]. Qed.

Lemma sb_lenpos : off = false -> 0 < LEN.
Proof using All.
  intros NOFF. unfold send_off in NOFF. apply orb_false_iff in NOFF as [_ N]. apply Z.eqb_neq in N.
  pose proof (zr_word (getr regs 11)) as R. unfold inr64 in R. lia.
Qed.

Lemma sb_blk_cases : forall j L1 A1 cap1 out1, sb_blk j L1 A1 cap1 out1 ->
  (bv_unsigned cap1 = 0 /\ bv_unsigned out1 = 0 /\ NO = 0 /\ O = [] /\ j = 0%nat /\ L1 = L /\ A1 = A) \/
  (0 < bv_unsigned cap1 /\ NO <= bv_unsigned cap1 /\ fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
   In (bv_unsigned out1, bv_unsigned cap1) (blocks L1 A1)).
Proof using All.
  intros j L1 A1 cap1 out1
    [(J & -> & -> & -> & ->)|(J & Cp & NOle & Cle & FRE & (b1 & b2 & c1 & c2 & E1 & E2 & E3) & NEQ)].
  - destruct H26 as [(C0 & O0 & N0 & OE)|(Cp & NOle & IN & FRE & _)].
    + left. exact (conj C0 (conj O0 (conj N0 (conj OE (conj J (conj eq_refl eq_refl)))))).
    + right. exact (conj Cp (conj NOle (conj FRE IN))).
  - right. split; [exact Cp|]. split; [exact NOle|]. split; [exact FRE|].
    rewrite E1. apply in_or_app. right. left. reflexivity.
Qed.

Lemma sb_fin : forall (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) (j : nat)
    (cap1 out1 : word) (Wpre : list ivl) (e0 k0 : Z) (ev0 nk0 : word) (r0 : Z) (m1n : word -> option byte)
    (ms1 can1 s1 : machine_state),
  ro_agree rsegs mem1 ->
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  sb_blk j L1 A1 cap1 out1 -> (live = true -> sb_res L1 A1 (bv_unsigned out1) k0 (bv_unsigned cap1)) ->
  st_init_done A1 = true ->
  off = false ->
  (live = false -> j = 0%nat /\ nk0 = nout /\ k0 = 0 /\ r0 = CAP - NO) ->
  (live = true -> bytes_at rsegs mem1 (bv_unsigned out1) O /\ bv_unsigned nk0 = NO + k0 /\
     k0 + r0 = bv_unsigned cap1 - NO /\ 0 <= k0 /\ 0 <= r0) ->
  rw_cells rsegs mem1 G_CLIENT [C4 (Z_to_bv 64 cl)] ->
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  munch Wpre (normalize rsegs mem1) m1n -> wmono rsegs (normalize rsegs mem1) m1n ->
  sb_fin_at cap1 out1 dd e0 k0 ev0 nk0 r0 m1n s1 ->
  ms_rel rsegs can1 s1 -> ro_same rsegs mem1 (ms_mem can1) -> Regs6ss.ms_eqv can1 ms1 ->
  sb_post (mkCfg ms1 md1).
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 Wpre e0 k0 ev0 nk0 r0 m1n ms1 can1 s1
    RO1 RP1 BLK RES1 INI1 NOFF NL LV CCL WPRE MU0 WM0 FIN REL ROS EQ.
  pose proof sb_tp as (TP1 & TP2 & TP3). pose proof sb_sp as (S1 & S2 & S3 & S4).
  pose proof H02 as (HM & HWF & HBD & HRA & _).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof H27 as MGR.
  pose proof (sb_blk_cases _ _ _ _ _ BLK) as BC.
  pose proof (sb_lenpos NOFF) as LPOS. pose proof sb_lo as LO.
  pose proof (zr_word cap1) as Rc1. pose proof (zr_word out1) as Ro1. pose proof (zr_word nk0) as Rn0.
  unfold inr64 in *.
  unfold sb_fin_at, sl_fin in FIN.
  destruct FIN as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & m2n & -> & MU1
                   & WM1 & ST2 & MI2 & BL2 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  rewrite CAN in EQ.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
  remember (ms_mem can1) as m3 eqn:Em3. clear Em3 CAN.
  pose proof (sb_munch_cat _ _ _ _ _ MU0 MU1) as MU01.
  pose proof (wmono_trans rsegs _ _ _ WM0 WM1) as WM01.
  destruct (sb_back mem1 m2n m3 _ RO1 HR ROS MU01 WM01) as (MU3 & WM3 & RO3).
  pose proof (sb_pres regs R3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 X3) as PRS.
  pose proof (ret_pc_of_ok _ HRA) as RPC. rewrite sb_getr in RPC.
  change (reg_get regs 1) with (getr regs 1). rewrite RPC.
  rewrite sb_etp in Q5.
  change (reg_get regs 10) with (getr regs 10) in BL2.
  change (reg_get regs 11) with (getr regs 11) in Q4, Q6.
  assert (PTd : dd = 0 -> bv_unsigned out1 + bv_unsigned nk0 - k0 = bv_unsigned out1 + NO /\
                          k0 + r0 = bv_unsigned cap1 - NO).
  { intros D. assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D).
    destruct (LV LIVE) as (_ & E1 & E2 & _). split; lia. }
  assert (RPm : relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs m3 md1).
  { eapply (sb_kA Bm API AX EU BW H01); [exact RP1 | exact MU3 | rewrite H01; exact WM3 | exact H14 |].
    intros a Ha.
    apply (sb_W_ok L1 A1 mem1 md1 j cap1 out1 Wpre); [exact RP1 | exact BLK | exact NOFF | | exact WPRE | exact PTd | exact Ha].
    intros _. destruct BC as [(Z0 & _ & N0 & _)|(Cp & NOle & _ & IN)];
      [split; [lia | intros; lia] | split; [exact NOle | intros; exact IN]]. }
  pose proof (sb_rp_regs _ _ _ _ _ _ _ _ _ _ _ _ _ RPm PRS) as RPf.
  assert (NIM : forall i, 0 <= i < k0 + r0 -> ~ in_img Bm (bv_unsigned out1 + bv_unsigned nk0 - k0 + i)).
  { intros i Hi. destruct (Z.eq_dec dd 0) as [D|D].
    - destruct (PTd D) as [E1 E2]. rewrite E1.
      destruct BC as [(Z0 & _)|(Cp & NOle & (_ & _ & FI) & _)]; [lia|].
      replace (bv_unsigned out1 + NO + i) with (bv_unsigned out1 + (NO + i)) by lia. apply FI. lia.
    - assert (LF : live = false) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_neq; exact D).
      destruct (NL LF) as (J0 & N0 & K0 & R0). subst nk0 k0 r0.
      destruct BLK as [(_ & _ & _ & -> & ->)|(Jp & _)]; [|lia].
      destruct H26 as [(C0 & _)|(Cp & NOle & _ & (_ & _ & FI) & _)]; [lia|].
      replace (OUT + NO - 0 + i) with (OUT + (NO + i)) by lia. apply FI. lia. }
  assert (CCL3 : rw_cells rsegs m3 G_CLIENT [C4 (Z_to_bv 64 cl)]).
  { apply (sb_rw_tr mem1 m3 _ _ CCL). intros i Hi. cbn [cells_size csize] in Hi.
    assert (OA : outside (Wpre ++ sl_wit (reg_get regs 4) (dd =? 0) (bv_unsigned out1 + bv_unsigned nk0 - k0)
                            (k0 + r0)) (G_CLIENT + i)).
    { apply sb_out_img; [exact WPRE | apply H13; lia | unfold G_CLIENT; lia | unfold G_CLIENT; lia
        | unfold G_CLIENT; lia | unfold G_CLIENT; lia | exact NIM]. }
    split.
    - apply (munch_mbyte rsegs _ _ _ _ MU3); [unfold G_CLIENT; lia | exact OA].
    - intros W. apply (proj1 (munch_writable rsegs _ _ _ (G_CLIENT + i) MU3 ltac:(unfold G_CLIENT; lia) OA)). exact W. }
  unfold sb_post.
  destruct (Z.eq_dec dd 0) as [D|D].
  - assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D).
    destruct (LV LIVE) as (OB & E1 & E2 & K0 & R0).
    rewrite (proj2 (Z.eqb_eq dd 0) D) in Q4, Q5.
    destruct (Q6 D) as (LE & junk' & CO).
    pose proof (sb_rw_back _ _ _ _ HR CO) as CO3.
    destruct BC as [(Z0 & _)|(Cp & NOle & FRE & IN)]; [lia|].
    pose proof FRE as (FR1 & FR2 & FI).
    destruct (RES1 LIVE) as (tp & qp & jr & o & LQ & NR & _ & _ & RT1 & RT3 & RT4 & RT5 & LV1).
    rewrite (sl_rest_fin (bv_unsigned mx) LEN NO k0 (bv_unsigned cap1) jr o) in RT3, RT4, RT5
      by (pose proof (zr_word mx) as Rmx; unfold inr64 in Rmx; lia).
    cbn [fst snd] in RT3, RT4, RT5. rewrite app_nil_r in RT3.
    exists L1, A1, R3, m3, md1, (bv_unsigned out1), (bv_unsigned cap1), junk'.
    split; [rewrite H01; reflexivity|].
    split; [exact RPf|]. split; [exact INI1|].
    split.
    { exists qp. rewrite <- RT3, <- RT5. split; [lia|]. split; [exact RT1|]. intros _. exact (LV1 Cp). }
    split; [rewrite H01; exact RO3|].
    split; [rewrite H01; exact (proj2 (bytes_at_rel rsegs m3 m2n _ _ HR) BL2)|].
    split; [rewrite H01; exact CCL3|].
    split; [rewrite NOFF, H01; exact (sb_rw_back _ _ _ _ HR Q1)|].
    split; [rewrite H01; exact (sb_rw_back _ _ _ _ HR Q2)|].
    split; [rewrite NOFF, H01; exact (sb_rw_back _ _ _ _ HR Q3)|].
    split; [intros LF; rewrite LIVE in LF; discriminate|].
    intros _.
    split; [lia|]. split; [exact RT4|]. split; [exact FRE|].
    split; [eexists; rewrite H01; exact (sb_rw_back _ _ _ _ HR Q5)|].
    split.
    { intros q m Hq Hne Hm. destruct BLK as [(_ & _ & _ & _ & ->)|(_ & _ & _ & _ & _ & _ & NEQ)];
        [exact Hne | exact (NEQ q m Hq Hne Hm)]. }
    split.
    { destruct BLK as [(_ & -> & -> & -> & ->)|(_ & _ & _ & _ & _ & DEC & _)]; [|exact DEC].
      destruct (in_split _ _ IN) as (b1 & b2 & EB).
      exists b1, b2, b1, b2. split; [exact EB|]. split; [reflexivity|]. right. split; [lia | exact EB]. }
    destruct CO3 as [[WF BT] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (WF1 & WF2 & _).
    cbn [cells_bytes cbytes] in BT. rewrite app_nil_r in BT.
    rewrite firstn_all2 in BT by lia.
    split.
    { rewrite H01. apply bytes_at_app. split.
      - apply (bytes_at_transfer rsegs mem1); [exact OB|]. intros i Hi.
        apply (munch_mbyte rsegs _ _ _ _ MU3); [lia|].
        apply sb_out_blk; [exact WPRE | lia | apply FI; lia | lia].
      - rewrite LO. replace (bv_unsigned out1 + NO) with (bv_unsigned out1 + bv_unsigned nk0 - k0) by lia. exact BT. }
    split; [rewrite WF2; lia|].
    rewrite H01. replace (bv_unsigned nk0 + (LEN - k0)) with (NO + LEN) in Q4 by lia.
    rewrite !Z_to_bv_lit_self. exact (sb_rw_back _ _ _ _ HR Q4).
  - assert (LF : live = false) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_neq; exact D).
    destruct (NL LF) as (J0 & N0 & K0 & R0). subst nk0 k0 r0 j.
    destruct BLK as [(_ & -> & -> & -> & ->)|(Jp & _)]; [|lia].
    assert (D1 : dd = 1) by (destruct H18; lia).
    rewrite (proj2 (Z.eqb_neq dd 0) D) in Q4, Q5.
    exists L, A, R3, m3, md1, 0, 0, [].
    split; [rewrite H01; reflexivity|].
    split; [exact RPf|]. split; [exact INI1|].
    split.
    { exists []. unfold send_line_tr. rewrite LF. split; [reflexivity|]. split; [exact H28|].
      intros LT; discriminate LT. }
    split; [rewrite H01; exact RO3|].
    split; [rewrite H01; exact (proj2 (bytes_at_rel rsegs m3 m2n _ _ HR) BL2)|].
    split; [rewrite H01; exact CCL3|].
    split; [rewrite NOFF, H01; exact (sb_rw_back _ _ _ _ HR Q1)|].
    split; [rewrite H01; exact (sb_rw_back _ _ _ _ HR Q2)|].
    split; [rewrite NOFF, H01; exact (sb_rw_back _ _ _ _ HR Q3)|].
    split.
    { intros _. split; [reflexivity|].
      rewrite NOFF, (proj2 (Z.eqb_eq dd 1) D1), H01. split; [exact (sb_rw_back _ _ _ _ HR Q5)|].
      exact (sb_rw_back _ _ _ _ HR Q4). }
    intros LT. rewrite LF in LT. discriminate.
Qed.

Definition sb_cregs (regs1 : bvmap 5 word) (k : Z) (nk1 out1 : word) (c1 : Z) : Prop :=
  getr regs1 1 = Z_to_bv 64 0x13454 /\ getr regs1 2 = Z_to_bv 64 (SP + -112) /\
  getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\ getr regs1 8 = getr regs 11 /\
  getr regs1 9 = getr regs 10 /\ getr regs1 10 = out1 /\ getr regs1 11 = Z_to_bv 64 (2 * (bv_unsigned nk1 + c1)) /\
  getr regs1 18 = Z_to_bv 64 (k + LINE) /\ getr regs1 19 = Z_to_bv 64 c1 /\
  getr regs1 20 = Z_to_bv 64 (2 * (bv_unsigned nk1 + c1)) /\
  getr regs1 21 = Z_to_bv 64 136040 /\ getr regs1 22 = Z_to_bv 64 202912 /\ getr regs1 23 = Z_to_bv 64 k /\
  getr regs1 24 = Z_to_bv 64 1 /\ getr regs1 25 = Z_to_bv 64 3 /\ getr regs1 26 = Z_to_bv 64 4 /\
  getr regs1 27 = nk1.

Definition sb_call (w : Z) (c : config) : Prop :=
  exists (L1 : layout) (A1 : astate) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
         (j : nat) (k : Z) (nk1 cap1 out1 : word) (junk1 jb : list byte) (c1 : Z),
    c = mkCfg (YK11.mkst regs1 (Z_to_bv 64 0x178f8) mem1 (seg_rom (ms_segs Bm))) md1 /\
    w = bv_unsigned cap1 /\ sb_cregs regs1 k nk1 out1 c1 /\ ro_agree rsegs mem1 /\
    relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 /\
    sb_blk j L1 A1 cap1 out1 /\ sb_res L1 A1 (bv_unsigned out1) k (bv_unsigned cap1) /\ st_init_done A1 = true /\
    off = false /\ dd = 0 /\
    0 <= k < LEN /\ bv_unsigned nk1 = NO + k /\ NO + k <= bv_unsigned cap1 /\
    1 <= c1 <= LEN - k /\ bv_unsigned cap1 < bv_unsigned nk1 + c1 /\
    c1 = (if bv_unsigned mx =? 0 then LEN - k else Z.min (LEN - k) (bv_unsigned mx)) /\
    rw_cells rsegs mem1 G_CLIENT [C4 (Z_to_bv 64 3)] /\
    rw_cells rsegs mem1 G_BROKEN [C1 (Z_to_bv 8 0)] /\ rw_cells rsegs mem1 G_DEAD [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs mem1 G_EINTR [C1 (Z_to_bv 8 0)] /\
    rw_cells rsegs mem1 G_OUTV [C8 mx; C8 nk1; C8 cap1; C8 out1] /\
    bytes_at rsegs mem1 LINE Bl /\ bytes_at rsegs mem1 (bv_unsigned out1) O /\
    rw_cells rsegs mem1 (bv_unsigned out1 + NO)
      [CB (Z.to_nat k) (firstn (Z.to_nat k) Bl); CB (Z.to_nat (bv_unsigned cap1 - NO - k)) junk1] /\
    rw_cells rsegs mem1 (SP + -112) [CB 8 jb; C8 (reg_get regs 27); C8 (reg_get regs 26); C8 (reg_get regs 25);
       C8 (reg_get regs 24); C8 (reg_get regs 23); C8 (reg_get regs 22); C8 (reg_get regs 21); C8 (reg_get regs 20);
       C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)].

Lemma sb_rp_run : forall L1 A1 mem1 md1 j cap1 out1 Wpre k0 (nk0 : word) r0 m3,
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  sb_blk j L1 A1 cap1 out1 -> off = false ->
  (live = true -> bv_unsigned nk0 = NO + k0 /\ k0 + r0 = bv_unsigned cap1 - NO) ->
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  munch (Wpre ++ sl_wit (reg_get regs 4) (dd =? 0) (bv_unsigned out1 + bv_unsigned nk0 - k0) (k0 + r0)) mem1 m3 ->
  wmono rsegs mem1 m3 ->
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs m3 md1.
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 Wpre k0 nk0 r0 m3 RP1 BLK NOFF LV WPRE MU3 WM3.
  pose proof (sb_blk_cases _ _ _ _ _ BLK) as BC.
  eapply (sb_kA Bm API AX EU BW H01); [exact RP1 | exact MU3 | rewrite H01; exact WM3 | exact H14 |].
  intros a Ha.
  apply (sb_W_ok L1 A1 mem1 md1 j cap1 out1 Wpre); [exact RP1 | exact BLK | exact NOFF | | exact WPRE | | exact Ha].
  - intros _. destruct BC as [(Z0 & _ & N0 & _)|(Cp & NOle & _ & IN)];
      [split; [lia | intros; lia] | split; [exact NOle | intros; exact IN]].
  - intros D. assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D).
    destruct (LV LIVE) as (E1 & E2). split; lia.
Qed.

Lemma sb_next : forall (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) (j : nat)
    (cap1 out1 : word) (Wpre : list ivl) (jb : list byte) (e0 k0 : Z) (ev0 nk0 : word) (r0 : Z)
    (m1n : word -> option byte) (ms1 can1 s1 : machine_state),
  ro_agree rsegs mem1 ->
  relay_post Bm API SEND_LINE_K EE FF L A regs mem md L1 A1 regs mem1 md1 ->
  sb_blk j L1 A1 cap1 out1 -> (live = true -> sb_res L1 A1 (bv_unsigned out1) k0 (bv_unsigned cap1)) ->
  st_init_done A1 = true ->
  off = false ->
  (live = true -> bytes_at rsegs mem1 (bv_unsigned out1) O /\ bv_unsigned nk0 = NO + k0 /\
     k0 + r0 = bv_unsigned cap1 - NO /\ 0 <= k0 /\ 0 <= r0) ->
  rw_cells rsegs mem1 G_CLIENT [C4 (Z_to_bv 64 cl)] ->
  (forall lo hi, In (lo, hi) Wpre -> (SP - 112 <= lo /\ hi <= SP) \/ (202984 <= lo /\ hi <= 203000)) ->
  munch Wpre (normalize rsegs mem1) m1n -> wmono rsegs (normalize rsegs mem1) m1n ->
  sb_call_at cap1 out1 jb dd e0 k0 ev0 nk0 r0 m1n s1 ->
  ms_rel rsegs can1 s1 -> ro_same rsegs mem1 (ms_mem can1) -> Regs6ss.ms_eqv can1 ms1 ->
  sb_call (bv_unsigned cap1) (mkCfg ms1 md1).
Proof using All.
  intros L1 A1 mem1 md1 j cap1 out1 Wpre jb e0 k0 ev0 nk0 r0 m1n ms1 can1 s1
    RO1 RP1 BLK RES1 INI1 NOFF LV CCL WPRE MU0 WM0 CALL REL ROS EQ.
  pose proof sb_tp as (TP1 & TP2 & TP3). pose proof sb_sp as (S1 & S2 & S3 & S4).
  pose proof (@YM05.alloc_ceiling_value rc) as ACV.
  pose proof (sb_blk_cases _ _ _ _ _ BLK) as BC.
  pose proof (sb_lenpos NOFF) as LPOS. pose proof sb_lo as LO.
  pose proof (zr_word cap1) as Rc1. pose proof (zr_word out1) as Ro1. pose proof (zr_word nk0) as Rn0.
  unfold inr64 in *.
  unfold sb_call_at, sl_call in CALL.
  destruct CALL as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & k' & ev' & nk' & r'
                    & junk' & m2n & c' & -> & INV & FRM & MU1 & WM1 & D0 & Hk' & Hnk' & Hkr' & Hc' & Hcap' & Hcd'
                    & [t' Ht']).
  assert (LIVE : live = true) by (unfold send_live; rewrite NOFF; cbn [negb andb]; apply Z.eqb_eq; exact D0).
  destruct (LV LIVE) as (OB & E1 & E2 & K0 & R0).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL) as [CAN HR].
  rewrite CAN in EQ.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ eq_refl eq_refl) as (R3 & -> & X3).
  remember (ms_mem can1) as m3 eqn:Em3. clear Em3 CAN.
  pose proof (sb_munch_cat _ _ _ _ _ MU0 MU1) as MU01.
  pose proof (wmono_trans rsegs _ _ _ WM0 WM1) as WM01.
  destruct (sb_back mem1 m2n m3 _ RO1 HR ROS MU01 WM01) as (MU3 & WM3 & RO3).
  pose proof (sb_rp_run L1 A1 mem1 md1 j cap1 out1 Wpre k0 nk0 r0 m3 RP1 BLK NOFF
    (fun L => conj (proj1 (proj2 (LV L))) (proj1 (proj2 (proj2 (LV L))))) WPRE MU3 WM3) as RPm.
  destruct INV as (Hk & _ & _ & Hr0 & _ & _ & _ & BL & _ & CBR & CDD & CEI & COV & _ & HO).
  destruct (HO eq_refl) as (_ & _ & _ & _ & CO).
  destruct FRM as [FR _].
  assert (NIM : forall i, 0 <= i < k0 + r0 -> ~ in_img Bm (bv_unsigned out1 + bv_unsigned nk0 - k0 + i)).
  { intros i Hi. destruct BC as [(Z0 & _ & N0 & _)|(Cp & NOle & (_ & _ & FI) & _)]; [lia|].
    replace (bv_unsigned out1 + bv_unsigned nk0 - k0 + i) with (bv_unsigned out1 + (NO + i)) by lia.
    apply FI. lia. }
  assert (CCL3 : rw_cells rsegs m3 G_CLIENT [C4 (Z_to_bv 64 cl)]).
  { apply (sb_rw_tr mem1 m3 _ _ CCL). intros i Hi. cbn [cells_size csize] in Hi.
    assert (OA : outside (Wpre ++ sl_wit (reg_get regs 4) (dd =? 0) (bv_unsigned out1 + bv_unsigned nk0 - k0)
                            (k0 + r0)) (G_CLIENT + i)).
    { apply sb_out_img; [exact WPRE | apply H13; lia | unfold G_CLIENT; lia | unfold G_CLIENT; lia
        | unfold G_CLIENT; lia | unfold G_CLIENT; lia | exact NIM]. }
    split.
    - apply (munch_mbyte rsegs _ _ _ _ MU3); [unfold G_CLIENT; lia | exact OA].
    - intros W. apply (proj1 (munch_writable rsegs _ _ _ (G_CLIENT + i) MU3 ltac:(unfold G_CLIENT; lia) OA)).
      exact W. }
  assert (CL3 : cl = 3).
  { destruct H16 as [C3|C3]; [exact C3|]. unfold send_off in NOFF. rewrite C3 in NOFF. discriminate. }
  assert (OB3 : bytes_at rsegs m3 (bv_unsigned out1) O).
  { apply (bytes_at_transfer rsegs mem1); [exact OB|]. intros i Hi.
    destruct BC as [(Z0 & O0 & N0 & OE & _)|(Cp & NOle & (FR1 & FR2 & FI) & IN)];
      [rewrite OE in Hi; cbn in Hi; lia|].
    apply (munch_mbyte rsegs _ _ _ _ MU3); [lia|].
    apply sb_out_blk; [exact WPRE | lia | apply FI; lia | lia]. }
  pose proof (zr_word mx) as Rmx. unfold inr64 in Rmx.
  change (reg_get regs 11) with (getr regs 11) in Hk', Hc', Hcd', CO.
  assert (RESk : sb_res L1 A1 (bv_unsigned out1) k' (bv_unsigned cap1)).
  { unfold sb_res. destruct (RES1 LIVE) as (tp & qp & jr & o & RT). exists tp, qp, jr, o.
    rewrite <- (sl_rest_path (bv_unsigned mx) LEN NO (bv_unsigned cap1) jr o t' k0 k') by (first [exact Ht' | lia]).
    exact RT. }
  exists L1, A1, R3, m3, md1, j, k', nk', cap1, out1, junk', jb, c'.
  split; [rewrite H01; reflexivity|].
  split; [reflexivity|].
  split.
  { unfold sb_cregs.
    repeat split; rewrite (getr_of_eqv _ _ _ X3) by reflexivity; simp_regs; reflexivity. }
  split; [exact RO3|]. split; [exact RPm|]. split; [exact BLK|]. split; [exact RESk|]. split; [exact INI1|].
  split; [exact NOFF|]. split; [exact D0|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hcap'|]. split; [exact Hcd'|].
  rewrite CL3 in CCL3.
  split; [exact CCL3|].
  split; [exact (sb_rw_back _ _ _ _ HR CBR)|]. split; [exact (sb_rw_back _ _ _ _ HR CDD)|].
  split; [exact (sb_rw_back _ _ _ _ HR CEI)|]. split; [exact (sb_rw_back _ _ _ _ HR COV)|].
  split; [change (reg_get regs 10) with (getr regs 10) in BL; exact (proj2 (bytes_at_rel rsegs m3 m2n _ _ HR) BL)|].
  split; [exact OB3|].
  split.
  { replace (bv_unsigned out1 + NO) with (bv_unsigned out1 + bv_unsigned nk' - k') by lia.
    replace (bv_unsigned cap1 - NO - k') with r' by lia. exact (sb_rw_back _ _ _ _ HR CO). }
  exact (sb_rw_back _ _ _ _ HR FR).
Qed.


End Main.

End SB.
