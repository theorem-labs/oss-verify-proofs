(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad PcapPrelim PcapTypes Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF Shadow RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Local Ltac ceil_facts := idtac.   (* [comment removed for export] *)

Section Blocks.
  Context {hptr : Type}.
  Definition cblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
  Definition cb_tok (b : cblock) : hptr := fst (fst b).
  Definition cb_addr (b : cblock) : Z := snd (fst b).
  Definition cb_size (b : cblock) : Z := snd b.

  (* [comment removed for export] *)
  Definition in_block (LB : list cblock) (a : Z) : Prop :=
    Exists (fun b => cb_addr b <= a < cb_addr b + cb_size b) LB.
  Definition iv_in_block (LB : list cblock) (iv : Z * Z) : Prop :=
    Exists (fun b => cb_addr b <= fst iv /\ snd iv <= cb_addr b + cb_size b) LB.

  #[using="Type"] Lemma in_block_In : forall LB a, in_block LB a <-> exists b, In b LB /\ cb_addr b <= a < cb_addr b + cb_size b.
  Proof. ceil_facts. intros LB a. unfold in_block. rewrite Exists_exists. reflexivity. Qed.
  #[using="Type"] Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
  Proof. ceil_facts. intros. unfold in_block. rewrite Exists_app. reflexivity. Qed.


  Definition apart (b b' : cblock) : Prop :=
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Fixpoint blocks_apart (LB : list cblock) : Prop :=
    match LB with [] => True | b :: LB' => Forall (apart b) LB' /\ blocks_apart LB' end.


  #[using="Type"] Lemma blocks_apart_In : forall LB b b', blocks_apart LB -> In b LB -> In b' LB -> b = b' \/ apart b b'.
  Proof. ceil_facts.
    induction LB as [|c LB IH]; intros b b' H Hb Hb'; [destruct Hb|].
    destruct H as [Hc H]. destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
    - left; reflexivity.
    - right. exact (proj1 (Forall_forall _ _) Hc _ Hb').
    - right. pose proof (proj1 (Forall_forall _ _) Hc _ Hb) as A. unfold apart in *. lia.
    - apply IH; assumption.
  Qed.

  #[using="Type"] Lemma blocks_apart_app_inv : forall L1 L2, blocks_apart (L1 ++ L2) ->
    blocks_apart L1 /\ blocks_apart L2 /\ (forall b b', In b L1 -> In b' L2 -> apart b b').
  Proof. ceil_facts.
    induction L1 as [|c L1 IH]; intros L2 H; cbn in *.
    - repeat split; auto. intros b b' [].
    - destruct H as [Hc H]. apply IH in H as (A & B & C). apply Forall_app in Hc as [Hc1 Hc2].
      repeat split; auto. intros b b' [<-|Hb] Hb'; [exact (proj1 (Forall_forall _ _) Hc2 _ Hb') | apply C; assumption].
  Qed.
End Blocks.
Definition agrees_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma agrees_on_refl : forall P m, agrees_on P m m.
Proof. ceil_facts. intros P m a _ _. auto. Qed.
Lemma agrees_on_trans : forall P m1 m2 m3, agrees_on P m1 m2 -> agrees_on P m2 m3 -> agrees_on P m1 m3.
Proof. ceil_facts. intros P m1 m2 m3 H1 H2 a Ha Hp. destruct (H1 a Ha Hp) as [E1 W1]. destruct (H2 a Ha Hp) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agrees_on_weaken : forall (P Q : Z -> Prop) m m', agrees_on P m m' -> (forall a, Q a -> P a) -> agrees_on Q m m'.
Proof. ceil_facts. intros P Q m m' H HQ a Ha Hq. apply H; auto. Qed.

(* [comment removed for export] *)
Lemma agrees_on_of_munch : forall (P : Z -> Prop) W m m',
  munch W m m' -> wmono asegs m m' -> (forall a, 0 <= a < 2^64 -> P a -> outside W a) -> agrees_on P m m'.
Proof. ceil_facts.
  intros P W m m' MU WM HP a Ha Hp. split.
  - apply MU. rewrite wa_unsigned by lia. apply HP; [exact Ha | exact Hp].
  - apply WM.
Qed.

Lemma agrees_bytes_at : forall P m m' A bs,
  agrees_on P m m' -> bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
Proof. ceil_facts.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma agrees_wr_at : forall P m m' A n,
  agrees_on P m m' -> wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
Proof. ceil_facts.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma agrees_rw_cells : forall P m m' A cs,
  agrees_on P m m' -> rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
Proof. ceil_facts.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply agrees_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply agrees_wr_at; eauto.
Qed.
Lemma agrees_stk : forall P m m' lo hi,
  agrees_on P m m' -> stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
Proof. ceil_facts.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HS a Ha) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fblock : Type := (fframe * Z * Z)%type.       (* [comment removed for export] *)
Definition fb_fn (fr : fblock) : fframe := fst (fst fr).
Definition fb_addr (fr : fblock) : Z := snd (fst fr).
Definition fb_size (fr : fblock) : Z := snd fr.
Definition in_frames (FL : list fblock) (a : Z) : Prop := Exists (fun fr => fb_addr fr <= a < fb_addr fr + fb_size fr) FL.
Lemma in_frames_In : forall FL a, in_frames FL a <-> exists fr, In fr FL /\ fb_addr fr <= a < fb_addr fr + fb_size fr.
Proof. intros FL a. unfold in_frames. rewrite Exists_exists. reflexivity. Qed.
Lemma in_frames_cons : forall fr FL a, in_frames FL a -> in_frames (fr :: FL) a.
Proof. intros fr FL a H. apply Exists_cons_tl. exact H. Qed.
(* [comment removed for export] *)
Definition in_frame_sh (FL : list fblock) (a : Z) : Prop :=
  Exists (fun fr => Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3) FL.
Lemma in_frame_sh_In : forall FL a, in_frame_sh FL a <-> exists fr, In fr FL /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3.
Proof. intros FL a. unfold in_frame_sh. rewrite Exists_exists. reflexivity. Qed.
Lemma in_frame_sh_cons : forall fr FL a, in_frame_sh FL a -> in_frame_sh (fr :: FL) a.
Proof. intros fr FL a H. apply Exists_cons_tl. exact H. Qed.
Lemma in_frames_incl : forall FL FL' a, incl FL FL' -> in_frames FL a -> in_frames FL' a.
Proof. intros FL FL' a HI H. apply in_frames_In in H as (fr & Hf & Hr). apply in_frames_In. exists fr. split; [apply HI; exact Hf| exact Hr]. Qed.
Lemma in_frame_sh_incl : forall FL FL' a, incl FL FL' -> in_frame_sh FL a -> in_frame_sh FL' a.
Proof. intros FL FL' a HI H. apply in_frame_sh_In in H as (fr & Hf & Hr). apply in_frame_sh_In. exists fr. split; [apply HI; exact Hf| exact Hr]. Qed.

(* [comment removed for export] *)
Definition nofr (FFS : list fframe) (FL : list fblock) : Prop := forall f, In f FFS -> ~ In f (map fb_fn FL).
Lemma nofr_sub : forall FFS FFS' FL, nofr FFS FL -> incl FFS' FFS -> nofr FFS' FL.
Proof. intros FFS FFS' FL H HI f Hf. apply H. apply HI. exact Hf. Qed.
Lemma nofr_cons : forall FFS fr FL, nofr FFS FL -> ~ In (fb_fn fr) FFS -> nofr FFS (fr :: FL).
Proof. intros FFS fr FL H HN f Hf [E|Hin]; [apply HN; rewrite E; exact Hf | exact (H f Hf Hin)]. Qed.

Section Keeps.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Definition client_keeps (FL : list fblock) (CL : list cblk) (SP : Z) (a : Z) : Prop :=
    SP <= a \/ in_block CL a \/ in_frames FL a \/ in_frame_sh FL a.

  #[using="Type"] Lemma keeps_rw_cells_stack : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs -> SP <= A -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  #[using="Type"] Lemma keeps_bytes_at_stack : forall (FL : list fblock) (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps FL CL SP) m m' -> bytes_at asegs m A bs -> SP <= A -> bytes_at asegs m' A bs.
  Proof. intros FL CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  #[using="Type"] Lemma keeps_rw_cells_block : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_block CL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. left. apply HA. exact Ha. Qed.
  #[using="Type"] Lemma keeps_bytes_at_block : forall (FL : list fblock) (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps FL CL SP) m m' -> bytes_at asegs m A bs ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> in_block CL a) -> bytes_at asegs m' A bs.
  Proof. intros FL CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. right. left. apply HA. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_rw_cells_frame : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_frames FL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. right. left. apply HA. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_rw_cells_frame_sh : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_frame_sh FL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. right. right. apply HA. exact Ha. Qed.

  #[using="Type"] Lemma client_keeps_weaken : forall (FL FL' : list fblock) (CL CL' : list cblk) SP SP' m m',
    agrees_on (client_keeps FL CL SP) m m' -> SP <= SP' -> (forall a, in_block CL' a -> in_block CL a) ->
    incl FL' FL ->
    agrees_on (client_keeps FL' CL' SP') m m'.
  Proof.
    intros FL FL' CL CL' SP SP' m m' AG HS HB HF. eapply agrees_on_weaken; [exact AG|].
    intros a [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; apply HB; exact Ha | right; right; left; eapply in_frames_incl; eassumption
                                | right; right; right; eapply in_frame_sh_incl; eassumption].
  Qed.

  #[using="Type"] Lemma in_block_cons : forall (b : cblk) CL a, in_block CL a -> in_block (b :: CL) a.
  Proof. intros b CL a Hin. unfold in_block in *. apply Exists_cons_tl. exact Hin. Qed.

  #[using="Type"] Lemma keeps_trans : forall (FL FL' : list fblock) (CL CL' : list cblk) SP SP' m m0 m',
    agrees_on (client_keeps FL CL SP) m m0 -> agrees_on (client_keeps FL' CL' SP') m0 m' -> SP' <= SP ->
    (forall a, in_block CL a -> in_block CL' a) -> incl FL FL' ->
    agrees_on (client_keeps FL CL SP) m m'.
  Proof.
    intros FL FL' CL CL' SP SP' m m0 m' A1 A2 HS HB HF. eapply agrees_on_trans; [exact A1|].
    eapply client_keeps_weaken; [exact A2| exact HS| exact HB| exact HF].
  Qed.
End Keeps.

(* [comment removed for export] *)
Definition client_globals : list (Z * Z) :=
  [(0x21020, 2); (0x21040, 10); (0x21060, 30); (0x210a0, 28); (0x210e0, 21); (0x21120, 22); (0x21160, 25); (0x211a0, 3); (0x211c0, 23);
   (0x21240, 45); (0x212a0, 31); (0x212e0, 3); (0x21300, 3); (0x21320, 54); (0x21380, 24); (0x213c0, 71); (0x21440, 20); (0x21480, 45);
   (0x214e0, 48); (0x21540, 47); (0x215a0, 43); (0x21640, 7); (0x21660, 18); (0x216a0, 33); (0x21700, 45); (0x217a0, 3); (0x21800, 7);
   (0x21820, 25); (0x21b80, 24); (0x21bc0, 71); (0x21c40, 40); (0x21ca0, 51); (0x21d00, 33); (0x21d60, 14); (0x21d80, 66); (0x21e00, 60);
   (0x21e60, 60); (0x21ec0, 67); (0x21f40, 67); (0x22000, 28); (0x22080, 24); (0x220c0, 96); (0x22140, 33); (0x221a0, 14); (0x221c0, 42);
   (0x22220, 53); (0x22280, 76); (0x22300, 66); (0x22380, 51); (0x223e0, 73); (0x22460, 34); (0x224c0, 59); (0x22520, 50); (0x22580, 36);
   (0x225e0, 60); (0x22640, 72); (0x226c0, 70); (0x22740, 64); (0x227a0, 75); (0x22820, 76); (0x228a0, 71); (0x22920, 65); (0x229a0, 74);
   (0x22a20, 96); (0x22aa0, 49); (0x22b00, 57); (0x22b60, 48); (0x22bc0, 96); (0x22c40, 60); (0x5e0c80, 8)].

Section BlocksA.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition arenaA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    exists RLO RHI, RLO <= A /\ A + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND
      /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
  #[using="Type"] Lemma arenaA_sub : forall RNG m A n A' n', arenaA RNG m A n -> A <= A' -> A' + n' <= A + n -> arenaA RNG m A' n'.
  Proof. intros RNG m A n A' n' (RLO & RHI & H1 & H2 & H) HA HB. exists RLO, RHI. split; [lia|]. split; [lia| exact H]. Qed.

  Definition blockA (RNG : footprint) (m : mem) (b : cblk) : Prop :=
    ablock_range (cb_addr b) (cb_size b) /\ 0 < cb_addr b
    /\ unpoisoned m (cb_addr b) (cb_addr b + cb_size b)
    /\ rng RNG (cb_addr b) (cb_size b) /\ rng RNG (shad (cb_addr b)) (nshad (cb_size b))
    /\ arenaA RNG m (cb_addr b) (cb_size b).

  (* [comment removed for export] *)
  Definition frameA (RNG : footprint) (m : mem) (fr : fblock) : Prop :=
    ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr + fb_size fr <= ATOP /\ fb_addr fr mod 64 = 0 /\ 64 <= fb_size fr
    /\ rng RNG (fb_addr fr) (fb_size fr) /\ rng RNG (Z.shiftr (fb_addr fr) 3 + 2147450880) (Z.shiftr (fb_size fr) 3)
    /\ fb_size fr mod 64 = 0 /\ wr_at asegs m (Z.shiftr (fb_addr fr) 3 + 2147450880) (Z.shiftr (fb_size fr) 3).

  (* [comment removed for export] *)
  Definition aobjA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    0 < A /\ A + n <= 2^47 /\ unpoisoned m A (A + n)
    /\ rng RNG A n /\ rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8))
    /\ arenaA RNG m A n /\ ablk A (A + n).
  (* [comment removed for export] *)
  Definition mobjA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    0 < A /\ A + n <= 2^47 /\ unpoisoned m A (A + n) /\ rng RNG A n /\ arenaA RNG m A n /\ app_blk A (A + n).
  #[using="Type"] Lemma mobjA_sub : forall RNG m A n A' n', mobjA RNG m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> mobjA RNG m A' n'.
  Proof.
    intros RNG m A n A' n' (H0 & H1 & H2 & H3 & H4 & H5) HA HB Hn.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact H2| lia| lia]|]. split; [eapply rng_sub; [exact H3| lia| lia]|].
    split; [eapply arenaA_sub; [exact H4| lia| lia]| eapply app_blk_sub; [exact H5| lia| lia| lia]].
  Qed.
  #[using="Type"] Lemma aobjA_mobjA : forall RNG m A n, aobjA RNG m A n -> 0 <= n -> mobjA RNG m A n.
  Proof.
    intros RNG m A n (H0 & H1 & H2 & H3 & _ & H5 & H6) Hn.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H5|]. apply ablk_app_blk; [exact H6| lia].
  Qed.
  (* [comment removed for export] *)
  Definition clocA (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    (exists b, In b CL /\ cb_addr b <= A /\ A + n <= cb_addr b + cb_size b)
    \/ (exists fr, In fr FL /\ fb_addr fr <= A /\ A + n <= fb_addr fr + fb_size fr).
  Definition cobjA (RNG : footprint) (m : mem) (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    clocA FL CL A n /\ aobjA RNG m A n.
  (* [comment removed for export] *)
  Definition robjA (RNG : footprint) (m : mem) (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    (clocA FL CL A n \/ (exists g, In g client_globals /\ fst g <= A /\ A + n <= fst g + snd g /\ fst g + snd g <= 0x32000))
    /\ mobjA RNG m A n.
  #[using="Type"] Lemma robjA_mobjA : forall RNG m FL (CL : list cblk) A n, robjA RNG m FL CL A n -> mobjA RNG m A n.
  Proof. intros RNG m FL CL A n [_ H]. exact H. Qed.
  #[using="Type"] Lemma cobjA_robjA : forall RNG m FL (CL : list cblk) A n, cobjA RNG m FL CL A n -> 0 <= n -> robjA RNG m FL CL A n.
  Proof. intros RNG m FL CL A n [LOC O] Hn. split; [left; exact LOC| apply aobjA_mobjA; assumption]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma wr_at_sub : forall (m : mem) A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> wr_at asegs m A' n'.
  Proof.
    intros m A n A' n' (H0 & H1 & H) HA HB. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
  Qed.
  #[using="Type"] Lemma static_mobjA : forall RNG m A n,
    0x10040 <= A -> A + n <= 0x602fc0 -> 0 <= n -> unpoisoned m A (A + n) ->
    wr_at asegs m 0x7fffa000 779776 -> rng RNG 0x10000 0x5f3000 -> rng RNG 0x7fffa000 779776 -> mobjA RNG m A n.
  Proof.
    intros RNG m A n HA HB Hn U W RI RS.
    split; [lia|]. split; [lia|]. split; [exact U|]. split; [eapply rng_sub; [exact RI| lia| lia]|].
    split.
    - exists (64 * (A / 64)), (64 * ((A + n + 63) / 64)).
      assert (E1 : shad (64 * (A / 64)) = 2147450880 + 8 * (A / 64)) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      assert (E2 : shad (64 * ((A + n + 63) / 64)) = 2147450880 + 8 * ((A + n + 63) / 64)) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      rewrite E1, E2. unfold KEND.
      split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
      split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [eapply wr_at_sub; [exact W| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]
             | eapply rng_sub; [exact RS| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]].
    - unfold app_blk, KLOW. split; [lia|]. left. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sobjA (L : alayout) (RNG : footprint) (m : mem) (SP A n : Z) : Prop :=
    SP <= A /\ A + n <= al_top L /\ unpoisoned m A (A + n) /\ rng RNG A n /\ rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8)).
  #[using="Type"] Lemma arenaA_sh_rng : forall RNG m A n, arenaA RNG m A n -> 0 <= A -> 0 <= n -> rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8)).
  Proof.
    intros RNG m A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & _ & HR) HA Hn.
    eapply rng_sub; [exact HR| |]; rewrite ?shad_div, ?nshad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma clocA_keeps : forall FL (CL : list cblk) SP A n a, clocA FL CL A n -> A <= a < A + n -> client_keeps FL CL SP a.
  Proof.
    intros FL CL SP A n a [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Ha.
    - right; left. apply in_block_In. exists b. split; [exact Hb| lia].
    - right; right; left. apply in_frames_In. exists fr. split; [exact Hf| lia].
  Qed.
End BlocksA.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).
Local Ltac ceil_facts := idtac.   (* [comment removed for export] *)

Section Blocks.
  Context {hptr : Type}.
  Definition cblock : Type := (hptr * Z * Z)%type.     (* [comment removed for export] *)
  Definition cb_tok (b : cblock) : hptr := fst (fst b).
  Definition cb_addr (b : cblock) : Z := snd (fst b).
  Definition cb_size (b : cblock) : Z := snd b.

  (* [comment removed for export] *)
  Definition in_block (LB : list cblock) (a : Z) : Prop :=
    Exists (fun b => cb_addr b <= a < cb_addr b + cb_size b) LB.
  Definition iv_in_block (LB : list cblock) (iv : Z * Z) : Prop :=
    Exists (fun b => cb_addr b <= fst iv /\ snd iv <= cb_addr b + cb_size b) LB.

  #[using="Type"] Lemma in_block_In : forall LB a, in_block LB a <-> exists b, In b LB /\ cb_addr b <= a < cb_addr b + cb_size b.
  Proof. ceil_facts. intros LB a. unfold in_block. rewrite Exists_exists. reflexivity. Qed.
  #[using="Type"] Lemma in_block_app : forall L1 L2 a, in_block (L1 ++ L2) a <-> in_block L1 a \/ in_block L2 a.
  Proof. ceil_facts. intros. unfold in_block. rewrite Exists_app. reflexivity. Qed.


  Definition apart (b b' : cblock) : Prop :=
    cb_addr b + cb_size b <= cb_addr b' \/ cb_addr b' + cb_size b' <= cb_addr b.
  Fixpoint blocks_apart (LB : list cblock) : Prop :=
    match LB with [] => True | b :: LB' => Forall (apart b) LB' /\ blocks_apart LB' end.


  #[using="Type"] Lemma blocks_apart_In : forall LB b b', blocks_apart LB -> In b LB -> In b' LB -> b = b' \/ apart b b'.
  Proof. ceil_facts.
    induction LB as [|c LB IH]; intros b b' H Hb Hb'; [destruct Hb|].
    destruct H as [Hc H]. destruct Hb as [<-|Hb]; destruct Hb' as [<-|Hb'].
    - left; reflexivity.
    - right. exact (proj1 (Forall_forall _ _) Hc _ Hb').
    - right. pose proof (proj1 (Forall_forall _ _) Hc _ Hb) as A. unfold apart in *. lia.
    - apply IH; assumption.
  Qed.

  #[using="Type"] Lemma blocks_apart_app_inv : forall L1 L2, blocks_apart (L1 ++ L2) ->
    blocks_apart L1 /\ blocks_apart L2 /\ (forall b b', In b L1 -> In b' L2 -> apart b b').
  Proof. ceil_facts.
    induction L1 as [|c L1 IH]; intros L2 H; cbn in *.
    - repeat split; auto. intros b b' [].
    - destruct H as [Hc H]. apply IH in H as (A & B & C). apply Forall_app in Hc as [Hc1 Hc2].
      repeat split; auto. intros b b' [<-|Hb] Hb'; [exact (proj1 (Forall_forall _ _) Hc2 _ Hb') | apply C; assumption].
  Qed.
End Blocks.
Definition agrees_on (P : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Lemma agrees_on_refl : forall P m, agrees_on P m m.
Proof. ceil_facts. intros P m a _ _. auto. Qed.
Lemma agrees_on_trans : forall P m1 m2 m3, agrees_on P m1 m2 -> agrees_on P m2 m3 -> agrees_on P m1 m3.
Proof. ceil_facts. intros P m1 m2 m3 H1 H2 a Ha Hp. destruct (H1 a Ha Hp) as [E1 W1]. destruct (H2 a Ha Hp) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma agrees_on_weaken : forall (P Q : Z -> Prop) m m', agrees_on P m m' -> (forall a, Q a -> P a) -> agrees_on Q m m'.
Proof. ceil_facts. intros P Q m m' H HQ a Ha Hq. apply H; auto. Qed.

(* [comment removed for export] *)
Lemma agrees_on_of_munch : forall (P : Z -> Prop) W m m',
  munch W m m' -> wmono asegs m m' -> (forall a, 0 <= a < 2^64 -> P a -> outside W a) -> agrees_on P m m'.
Proof. ceil_facts.
  intros P W m m' MU WM HP a Ha Hp. split.
  - apply MU. rewrite wa_unsigned by lia. apply HP; [exact Ha | exact Hp].
  - apply WM.
Qed.

Lemma agrees_bytes_at : forall P m m' A bs,
  agrees_on P m m' -> bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
Proof. ceil_facts.
  intros P m m' A bs HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd. destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _].
  rewrite E. reflexivity.
Qed.
Lemma agrees_wr_at : forall P m m' A n,
  agrees_on P m m' -> wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
Proof. ceil_facts.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.
Lemma agrees_rw_cells : forall P m m' A cs,
  agrees_on P m m' -> rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
Proof. ceil_facts.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply agrees_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply agrees_wr_at; eauto.
Qed.
Lemma agrees_stk : forall P m m' lo hi,
  agrees_on P m m' -> stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
Proof. ceil_facts.
  intros P m m' lo hi HP (H0 & H1 & HS) HR. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (HP a ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HS a Ha) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fblock : Type := (fframe * Z * Z)%type.       (* [comment removed for export] *)
Definition fb_fn (fr : fblock) : fframe := fst (fst fr).
Definition fb_addr (fr : fblock) : Z := snd (fst fr).
Definition fb_size (fr : fblock) : Z := snd fr.
Definition in_frames (FL : list fblock) (a : Z) : Prop := Exists (fun fr => fb_addr fr <= a < fb_addr fr + fb_size fr) FL.
Lemma in_frames_In : forall FL a, in_frames FL a <-> exists fr, In fr FL /\ fb_addr fr <= a < fb_addr fr + fb_size fr.
Proof. intros FL a. unfold in_frames. rewrite Exists_exists. reflexivity. Qed.
Lemma in_frames_cons : forall fr FL a, in_frames FL a -> in_frames (fr :: FL) a.
Proof. intros fr FL a H. apply Exists_cons_tl. exact H. Qed.
(* [comment removed for export] *)
Definition in_frame_sh (FL : list fblock) (a : Z) : Prop :=
  Exists (fun fr => Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3) FL.
Lemma in_frame_sh_In : forall FL a, in_frame_sh FL a <-> exists fr, In fr FL /\ Z.shiftr (fb_addr fr) 3 + 2147450880 <= a < Z.shiftr (fb_addr fr) 3 + 2147450880 + Z.shiftr (fb_size fr) 3.
Proof. intros FL a. unfold in_frame_sh. rewrite Exists_exists. reflexivity. Qed.
Lemma in_frame_sh_cons : forall fr FL a, in_frame_sh FL a -> in_frame_sh (fr :: FL) a.
Proof. intros fr FL a H. apply Exists_cons_tl. exact H. Qed.
Lemma in_frames_incl : forall FL FL' a, incl FL FL' -> in_frames FL a -> in_frames FL' a.
Proof. intros FL FL' a HI H. apply in_frames_In in H as (fr & Hf & Hr). apply in_frames_In. exists fr. split; [apply HI; exact Hf| exact Hr]. Qed.
Lemma in_frame_sh_incl : forall FL FL' a, incl FL FL' -> in_frame_sh FL a -> in_frame_sh FL' a.
Proof. intros FL FL' a HI H. apply in_frame_sh_In in H as (fr & Hf & Hr). apply in_frame_sh_In. exists fr. split; [apply HI; exact Hf| exact Hr]. Qed.

(* [comment removed for export] *)
Definition nofr (FFS : list fframe) (FL : list fblock) : Prop := forall f, In f FFS -> ~ In f (map fb_fn FL).
Lemma nofr_sub : forall FFS FFS' FL, nofr FFS FL -> incl FFS' FFS -> nofr FFS' FL.
Proof. intros FFS FFS' FL H HI f Hf. apply H. apply HI. exact Hf. Qed.
Lemma nofr_cons : forall FFS fr FL, nofr FFS FL -> ~ In (fb_fn fr) FFS -> nofr FFS (fr :: FL).
Proof. intros FFS fr FL H HN f Hf [E|Hin]; [apply HN; rewrite E; exact Hf | exact (H f Hf Hin)]. Qed.

Section Keeps.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  Definition client_keeps (FL : list fblock) (CL : list cblk) (SP : Z) (a : Z) : Prop :=
    SP <= a \/ in_block CL a \/ in_frames FL a \/ in_frame_sh FL a.

  #[using="Type"] Lemma keeps_rw_cells_stack : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs -> SP <= A -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  #[using="Type"] Lemma keeps_bytes_at_stack : forall (FL : list fblock) (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps FL CL SP) m m' -> bytes_at asegs m A bs -> SP <= A -> bytes_at asegs m' A bs.
  Proof. intros FL CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. left. lia. Qed.
  #[using="Type"] Lemma keeps_rw_cells_block : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_block CL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. left. apply HA. exact Ha. Qed.
  #[using="Type"] Lemma keeps_bytes_at_block : forall (FL : list fblock) (CL : list cblk) SP m m' A bs,
    agrees_on (client_keeps FL CL SP) m m' -> bytes_at asegs m A bs ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> in_block CL a) -> bytes_at asegs m' A bs.
  Proof. intros FL CL SP m m' A bs AG HC HA. eapply agrees_bytes_at; [exact AG|exact HC|]. intros a Ha. right. left. apply HA. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_rw_cells_frame : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_frames FL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. right. left. apply HA. exact Ha. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma keeps_rw_cells_frame_sh : forall (FL : list fblock) (CL : list cblk) SP m m' A cs,
    agrees_on (client_keeps FL CL SP) m m' -> rw_cells asegs m A cs ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> in_frame_sh FL a) -> rw_cells asegs m' A cs.
  Proof. intros FL CL SP m m' A cs AG HC HA. eapply agrees_rw_cells; [exact AG|exact HC|]. intros a Ha. right. right. right. apply HA. exact Ha. Qed.

  #[using="Type"] Lemma client_keeps_weaken : forall (FL FL' : list fblock) (CL CL' : list cblk) SP SP' m m',
    agrees_on (client_keeps FL CL SP) m m' -> SP <= SP' -> (forall a, in_block CL' a -> in_block CL a) ->
    incl FL' FL ->
    agrees_on (client_keeps FL' CL' SP') m m'.
  Proof.
    intros FL FL' CL CL' SP SP' m m' AG HS HB HF. eapply agrees_on_weaken; [exact AG|].
    intros a [Ha|[Ha|[Ha|Ha]]]; [left; lia | right; left; apply HB; exact Ha | right; right; left; eapply in_frames_incl; eassumption
                                | right; right; right; eapply in_frame_sh_incl; eassumption].
  Qed.

  #[using="Type"] Lemma in_block_cons : forall (b : cblk) CL a, in_block CL a -> in_block (b :: CL) a.
  Proof. intros b CL a Hin. unfold in_block in *. apply Exists_cons_tl. exact Hin. Qed.

  #[using="Type"] Lemma keeps_trans : forall (FL FL' : list fblock) (CL CL' : list cblk) SP SP' m m0 m',
    agrees_on (client_keeps FL CL SP) m m0 -> agrees_on (client_keeps FL' CL' SP') m0 m' -> SP' <= SP ->
    (forall a, in_block CL a -> in_block CL' a) -> incl FL FL' ->
    agrees_on (client_keeps FL CL SP) m m'.
  Proof.
    intros FL FL' CL CL' SP SP' m m0 m' A1 A2 HS HB HF. eapply agrees_on_trans; [exact A1|].
    eapply client_keeps_weaken; [exact A2| exact HS| exact HB| exact HF].
  Qed.
End Keeps.

(* [comment removed for export] *)
Definition client_globals : list (Z * Z) :=
  [(0x21020, 2); (0x21040, 10); (0x21060, 30); (0x210a0, 28); (0x210e0, 21); (0x21120, 22); (0x21160, 25); (0x211a0, 3); (0x211c0, 23);
   (0x21240, 45); (0x212a0, 31); (0x212e0, 3); (0x21300, 3); (0x21320, 54); (0x21380, 24); (0x213c0, 71); (0x21440, 20); (0x21480, 45);
   (0x214e0, 48); (0x21540, 47); (0x215a0, 43); (0x21640, 7); (0x21660, 18); (0x216a0, 33); (0x21700, 45); (0x217a0, 3); (0x21800, 7);
   (0x21820, 25); (0x21b80, 24); (0x21bc0, 71); (0x21c40, 40); (0x21ca0, 51); (0x21d00, 33); (0x21d60, 14); (0x21d80, 66); (0x21e00, 60);
   (0x21e60, 60); (0x21ec0, 67); (0x21f40, 67); (0x22000, 28); (0x22080, 24); (0x220c0, 96); (0x22140, 33); (0x221a0, 14); (0x221c0, 42);
   (0x22220, 53); (0x22280, 76); (0x22300, 66); (0x22380, 51); (0x223e0, 73); (0x22460, 34); (0x224c0, 59); (0x22520, 50); (0x22580, 36);
   (0x225e0, 60); (0x22640, 72); (0x226c0, 70); (0x22740, 64); (0x227a0, 75); (0x22820, 76); (0x228a0, 71); (0x22920, 65); (0x229a0, 74);
   (0x22a20, 96); (0x22aa0, 49); (0x22b00, 57); (0x22b60, 48); (0x22bc0, 96); (0x22c40, 60); (0x5e1080, 8)].

Section BlocksA.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {hptr : Type}.
  Notation cblk := (@cblock hptr).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition arenaA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    exists RLO RHI, RLO <= A /\ A + n <= RHI /\ RLO mod 64 = 0 /\ RHI mod 64 = 0 /\ 0 <= RLO /\ RHI <= KEND
      /\ wr_at asegs m (shad RLO) (shad RHI - shad RLO) /\ rng RNG (shad RLO) (shad RHI - shad RLO).
  #[using="Type"] Lemma arenaA_sub : forall RNG m A n A' n', arenaA RNG m A n -> A <= A' -> A' + n' <= A + n -> arenaA RNG m A' n'.
  Proof. intros RNG m A n A' n' (RLO & RHI & H1 & H2 & H) HA HB. exists RLO, RHI. split; [lia|]. split; [lia| exact H]. Qed.

  Definition blockA (RNG : footprint) (m : mem) (b : cblk) : Prop :=
    ablock_range (cb_addr b) (cb_size b) /\ 0 < cb_addr b
    /\ unpoisoned m (cb_addr b) (cb_addr b + cb_size b)
    /\ rng RNG (cb_addr b) (cb_size b) /\ rng RNG (shad (cb_addr b)) (nshad (cb_size b))
    /\ arenaA RNG m (cb_addr b) (cb_size b).

  (* [comment removed for export] *)
  Definition frameA (RNG : footprint) (m : mem) (fr : fblock) : Prop :=
    ablk (fb_addr fr) (fb_addr fr + fb_size fr) /\ fb_addr fr + fb_size fr <= ATOP /\ fb_addr fr mod 64 = 0 /\ 64 <= fb_size fr
    /\ rng RNG (fb_addr fr) (fb_size fr) /\ rng RNG (Z.shiftr (fb_addr fr) 3 + 2147450880) (Z.shiftr (fb_size fr) 3)
    /\ fb_size fr mod 64 = 0 /\ wr_at asegs m (Z.shiftr (fb_addr fr) 3 + 2147450880) (Z.shiftr (fb_size fr) 3).

  (* [comment removed for export] *)
  Definition aobjA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    0 < A /\ A + n <= 2^47 /\ unpoisoned m A (A + n)
    /\ rng RNG A n /\ rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8))
    /\ arenaA RNG m A n /\ ablk A (A + n).
  (* [comment removed for export] *)
  Definition mobjA (RNG : footprint) (m : mem) (A n : Z) : Prop :=
    0 < A /\ A + n <= 2^47 /\ unpoisoned m A (A + n) /\ rng RNG A n /\ arenaA RNG m A n /\ app_blk A (A + n).
  #[using="Type"] Lemma mobjA_sub : forall RNG m A n A' n', mobjA RNG m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> mobjA RNG m A' n'.
  Proof.
    intros RNG m A n A' n' (H0 & H1 & H2 & H3 & H4 & H5) HA HB Hn.
    split; [lia|]. split; [lia|]. split; [eapply unpoisoned_sub; [exact H2| lia| lia]|]. split; [eapply rng_sub; [exact H3| lia| lia]|].
    split; [eapply arenaA_sub; [exact H4| lia| lia]| eapply app_blk_sub; [exact H5| lia| lia| lia]].
  Qed.
  #[using="Type"] Lemma aobjA_mobjA : forall RNG m A n, aobjA RNG m A n -> 0 <= n -> mobjA RNG m A n.
  Proof.
    intros RNG m A n (H0 & H1 & H2 & H3 & _ & H5 & H6) Hn.
    split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H5|]. apply ablk_app_blk; [exact H6| lia].
  Qed.
  (* [comment removed for export] *)
  Definition clocA (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    (exists b, In b CL /\ cb_addr b <= A /\ A + n <= cb_addr b + cb_size b)
    \/ (exists fr, In fr FL /\ fb_addr fr <= A /\ A + n <= fb_addr fr + fb_size fr).
  Definition cobjA (RNG : footprint) (m : mem) (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    clocA FL CL A n /\ aobjA RNG m A n.
  (* [comment removed for export] *)
  Definition robjA (RNG : footprint) (m : mem) (FL : list fblock) (CL : list cblk) (A n : Z) : Prop :=
    (clocA FL CL A n \/ (exists g, In g client_globals /\ fst g <= A /\ A + n <= fst g + snd g /\ fst g + snd g <= 0x32000))
    /\ mobjA RNG m A n.
  #[using="Type"] Lemma robjA_mobjA : forall RNG m FL (CL : list cblk) A n, robjA RNG m FL CL A n -> mobjA RNG m A n.
  Proof. intros RNG m FL CL A n [_ H]. exact H. Qed.
  #[using="Type"] Lemma cobjA_robjA : forall RNG m FL (CL : list cblk) A n, cobjA RNG m FL CL A n -> 0 <= n -> robjA RNG m FL CL A n.
  Proof. intros RNG m FL CL A n [LOC O] Hn. split; [left; exact LOC| apply aobjA_mobjA; assumption]. Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma wr_at_sub : forall (m : mem) A n A' n', wr_at asegs m A n -> A <= A' -> A' + n' <= A + n -> wr_at asegs m A' n'.
  Proof.
    intros m A n A' n' (H0 & H1 & H) HA HB. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A' + i) with (A + (A' - A + i)) by lia. apply H. lia.
  Qed.
  #[using="Type"] Lemma static_mobjA : forall RNG m A n,
    0x10040 <= A -> A + n <= 0x603fc0 -> 0 <= n -> unpoisoned m A (A + n) ->
    wr_at asegs m 0x7fffa000 780288 -> rng RNG 0x10000 0x5f4000 -> rng RNG 0x7fffa000 780288 -> mobjA RNG m A n.
  Proof.
    intros RNG m A n HA HB Hn U W RI RS.
    split; [lia|]. split; [lia|]. split; [exact U|]. split; [eapply rng_sub; [exact RI| lia| lia]|].
    split.
    - exists (64 * (A / 64)), (64 * ((A + n + 63) / 64)).
      assert (E1 : shad (64 * (A / 64)) = 2147450880 + 8 * (A / 64)) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      assert (E2 : shad (64 * ((A + n + 63) / 64)) = 2147450880 + 8 * ((A + n + 63) / 64)) by (rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia).
      rewrite E1, E2. unfold KEND.
      split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|]. split; [rewrite Z.mul_comm; apply Z.mod_mul; lia|].
      split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
      split; [eapply wr_at_sub; [exact W| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]
             | eapply rng_sub; [exact RS| Z.div_mod_to_equations; lia| Z.div_mod_to_equations; lia]].
    - unfold app_blk, KLOW. split; [lia|]. left. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sobjA (L : alayout) (RNG : footprint) (m : mem) (SP A n : Z) : Prop :=
    SP <= A /\ A + n <= al_top L /\ unpoisoned m A (A + n) /\ rng RNG A n /\ rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8)).
  #[using="Type"] Lemma arenaA_sh_rng : forall RNG m A n, arenaA RNG m A n -> 0 <= A -> 0 <= n -> rng RNG (shad (A - A mod 8)) (nshad (n + A mod 8)).
  Proof.
    intros RNG m A n (RLO & RHI & H1 & H2 & H3 & H4 & H5 & H6 & _ & HR) HA Hn.
    eapply rng_sub; [exact HR| |]; rewrite ?shad_div, ?nshad_div; unfold ASHOFF; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma clocA_keeps : forall FL (CL : list cblk) SP A n a, clocA FL CL A n -> A <= a < A + n -> client_keeps FL CL SP a.
  Proof.
    intros FL CL SP A n a [(b & Hb & H1 & H2)|(fr & Hf & H1 & H2)] Ha.
    - right; left. apply in_block_In. exists b. split; [exact Hb| lia].
    - right; right; left. apply in_frames_In. exists fr. split; [exact Hf| lia].
  Qed.
End BlocksA.
End TwB.
