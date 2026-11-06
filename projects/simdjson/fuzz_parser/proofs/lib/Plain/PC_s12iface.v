(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import Stdio_pure Printf_pieces.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RMallocRep RMallocTree RMalloc_iface ROpNew_iface ROpNew ROpNew_nt.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Malloc HarnessP ProgP SjStage1 SjS1Bytes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PC_kit PU_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Notation mem := (word -> option byte).

Section CANSEC1. Context {rc : runConstT}.
Definition PSTAGE1 : Z := 0x27d10.
Definition PSTAGE2 : Z := 0x29224.
Definition PPARSE : Z := 0x381dc.
Definition PS1_STACK : Z := 416.                              (* [comment removed for export] *)
Definition PS2_STACK : Z := 368 + 4096 + OPNEW_NT_STACK.      (* [comment removed for export] *)
Definition PARSE_STACK : Z := PS2_STACK.                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition hrange (A n : Z) : Prop := 0 < A /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0xa9000 <= A).
Lemma hrange_of_block : forall A n, rblock_range A n -> hrange A n.
Proof. intros A n (H1 & H2 & H3 & H4 & H5). split; [lia|]. split; [lia|]. split; [lia| exact H5]. Qed.
Lemma hrange_sub : forall A n A' n', hrange A n -> A <= A' -> 0 < A' -> 0 <= n' -> A' + n' <= A + n -> hrange A' n'.
Proof. intros A n A' n' (H1 & H2 & H3 & H4) Ha Ha' Hn Hb. split; [lia|]. split; [lia|]. split; [lia|]. lia. Qed.

(* [comment removed for export] *)
Definition rheap_pres_W (LB : list block) (SP : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

Lemma rheap_pres_W_stk : forall LB SP W m m' lo hi, rheap_pres_W LB SP W m m' -> stk psegs m lo hi -> SP <= lo ->
  (forall a, lo <= a < hi -> outside W a) -> stk psegs m' lo hi.
Proof.
  intros LB SP W m m' lo hi HP (H0 & H1 & HW) HS HX. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(left; lia) (HX i Hi)) as [E W']. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W', W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma rheap_pres_W_trans : forall LB SP W m1 m2 m3,
  rheap_pres_W LB SP W m1 m2 -> rheap_pres_W LB SP W m2 m3 -> rheap_pres_W LB SP W m1 m3.
Proof.
  intros LB SP W m1 m2 m3 H1 H2 a Ha Hc Hx. destruct (H1 a Ha Hc Hx) as [E1 W1]. destruct (H2 a Ha Hc Hx) as [E2 W2].
  split; [congruence| auto].
Qed.
Lemma rheap_pres_W_of_munch : forall LB SP W W' m m', munch W' m m' -> wmono psegs m m' ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a -> outside W' a) -> rheap_pres_W LB SP W m m'.
Proof.
  intros LB SP W W' m m' MU WM HW a Ha Hc Hx. split.
  - apply MU. unfold wa. rewrite unsigned_lit by lia. apply HW; assumption.
  - intros Hv. apply WM. exact Hv.
Qed.
Lemma rheap_pres_W_of_x : forall L LB SP SP' W X n m m', rheap_pres_x L SP' X n m m' -> SP' <= SP -> (forall b, In b LB -> In b L) ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a -> ~ (X <= a < X + n)) -> rheap_pres_W LB SP W m m'.
Proof.
  intros L LB SP SP' W X n m m' H HS HL HX a Ha Hc Hw. apply H; [exact Ha| | exact (HX a Ha Hc Hw)].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.
Lemma rheap_pres_W_of_pres : forall L LB SP SP' W m m', rheap_pres L SP' m m' -> SP' <= SP -> (forall b, In b LB -> In b L) ->
  rheap_pres_W LB SP W m m'.
Proof.
  intros L LB SP SP' W m m' H HS HL a Ha Hc _. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.
Lemma rheap_pres_W_of_W : forall L LB SP SP' W W' m m', rheap_pres_W L SP' W' m m' -> SP' <= SP -> (forall b, In b LB -> In b L) ->
  (forall a, 0 <= a < 2^64 -> rclient_addr LB SP a -> outside W a -> outside W' a) -> rheap_pres_W LB SP W m m'.
Proof.
  intros L LB SP SP' W W' m m' H HS HL HW a Ha Hc Hw. apply H; [exact Ha| | exact (HW a Ha Hc Hw)].
  destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [left; lia| right; left; exact Hc| right; right; exists b; split; [apply HL; exact Hb| exact Hr]].
Qed.
(* [comment removed for export] *)
Lemma rheap_pres_bytes_at' : forall LB SP m m' A bs, rheap_pres LB SP m m' -> bytes_at psegs m A bs ->
  rclient_range LB SP A (Z.of_nat (length bs)) -> bytes_at psegs m' A bs.
Proof. intros. eapply rheap_pres_bytes_at; eassumption. Qed.

Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn; [tauto|]. rewrite IH. tauto.
Qed.

Lemma rheap_pres_W_rw_cells : forall LB SP W m m' A cs, rheap_pres_W LB SP W m m' -> rw_cells psegs m A cs ->
  rclient_range LB SP A (Z.of_nat (cells_size cs)) -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells psegs m' A cs.
Proof.
  intros LB SP W m m' A cs HP [[Hwf (B0 & B1 & HB)] (W0 & W1 & WW)] HR HD. split; [split; [exact Hwf|]|].
  - rewrite cells_bytes_length in B1 by exact Hwf. split; [exact B0|]. split; [rewrite cells_bytes_length by exact Hwf; exact B1|].
    intros i Hi. rewrite <- (HB i Hi). rewrite cells_bytes_length in Hi by exact Hwf. unfold mrd.
    destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(eapply disjoint_outside; [exact HD| lia])) as [E _].
    rewrite E. reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    destruct (HP (A + i) ltac:(lia) ltac:(eapply rclient_range_addr; [exact HR|lia]) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ WV].
    apply WV. apply WW. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition s1_win (SP THIS ASI len : Z) : list (Z * Z) :=
  [(SP - PS1_STACK, SP); (THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 88); (ASI, ASI + 4 * len + 36)].

Definition s1l_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (m : mem) (THIS BUF ASI : Z) (d : list Z) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (rcv : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rcv) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ frm0 fc' /\ 0 <= rcv < 2^64
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp) /\ wmono psegs m m'
    /\ munch (s1_win (bv_unsigned sp) THIS ASI (zlength d)) m m'
    /\ (rcv = 0 <-> fst (scan d) = true)
    /\ rw_cells psegs m' (THIS + 72) [C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d))]
    /\ (rcv = 0 -> rw_cells psegs m' (THIS + 8) [C4 (Z_to_bv 64 (zlength (snd (scan d))))]
                 /\ rw_cells psegs m' (THIS + 24) [C4 (Z_to_bv 64 0)]
                 /\ rw_cells psegs m' ASI [CB (4 * (length (snd (scan d)) + 3)) (u32bytes (snd (scan d) ++ [zlength d; zlength d; 0]))]).

Definition s1l_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (THIS BUF ASI : Z) (d : list Z) (lo : Z),
    bytes_at psegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    hrange BUF (zlength d + 64) -> 16 <= BUF -> hrange THIS 96 -> hrange ASI (4 * zlength d + 36) -> THIS mod 16 = 0 -> ASI mod 16 = 0 ->
    (BUF + zlength d + 64 <= THIS \/ THIS + 96 <= BUF) -> (BUF + zlength d + 64 <= ASI \/ ASI + 4 * zlength d + 36 <= BUF) ->
    (THIS + 96 <= ASI \/ ASI + 4 * zlength d + 36 <= THIS) ->
    wr_at psegs m THIS 96 -> rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] -> wr_at psegs m ASI (4 * zlength d + 36) ->
    stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PS1_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
    mem_inv psegs m -> frm0 fc ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 (zlength d) -> a3 = Z_to_bv 64 0 ->
    evt psegs (s1l_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m THIS BUF ASI d lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PSTAGE1) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rn_copy (d idx : list Z) : Monad.M PState unit :=
  match idx with
  | i0 :: _ => if is_numstart (byte_at d i0)
               then c <- HarnessP.opnew raw_malloc ProgP.new_handler (zlength d - i0 + 64) ;; HarnessP.opdelete raw_free c
               else mret tt
  | [] => mret tt
  end.

(* [comment removed for export] *)
Definition s2_win (THIS ATP ntp ASB nsb AOC AIA : Z) : list (Z * Z) :=
  [(THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (ATP, ATP + ntp); (ASB, ASB + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)].

Definition s2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (s : PState) (LB : list block) (lo B : Z) (W : list (Z * Z)) (m : mem) (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom psegs)
    /\ frm0 fc'
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rheap_pres_W LB (bv_unsigned sp) W m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' LB m'.

Definition stage2_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B : Z) (errv : word) (d idx : list Z)
         (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
         (x24 x88 : word) (jtp jsb joc jia : list byte),
    RHEAP s LB m ->
    (* [comment removed for export] *)
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (psi, ASI, nsi) LB -> 4 * zlength idx + 12 <= nsi ->
    In (pcp, ACP, ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB -> In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    (* [comment removed for export] *)
    ntp mod 8 = 0 -> 8 * (zlength idx + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    (* [comment removed for export] *)
    bytes_at psegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    scan d = (true, idx) ->
    rw_cells psegs m ASI [CB (4 * (length idx + 3)) (u32bytes (idx ++ [zlength d; zlength d; 0]))] ->
    (* [comment removed for export] *)
    rw_cells psegs m (THIS + 8) [C4 (Z_to_bv 64 (zlength idx))] -> rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells psegs m (THIS + 24) [C4 x24] ->
    rw_cells psegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 (Z_to_bv 64 BUF); C8 (Z_to_bv 64 (zlength d)); C8 x88] ->
    (* [comment removed for export] *)
    rw_cells psegs m DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] -> bv_unsigned sp <= DOC -> DOC + 16 <= B -> DOC mod 8 = 0 ->
    rw_cells psegs m ATP [CB (Z.to_nat ntp) jtp] -> rw_cells psegs m ASB [CB (Z.to_nat nsb) jsb] ->
    rw_cells psegs m AOC [CB 8192 joc] -> rw_cells psegs m AIA [CB 1024 jia] ->
    (* [comment removed for export] *)
    rw_cells psegs m PFMIN fmin_cells -> rw_cells psegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
    (* [comment removed for export] *)
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PS2_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
    rw_cells psegs m (errno_addr tp) [C4 errv] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 DOC ->
    implM psegs (rn_copy d idx) s
          (s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B (s2_win THIS ATP ntp ASB nsb AOC AIA) m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PSTAGE2) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_win (SP THIS ASI len ATP ntp ASB nsb AOC AIA : Z) : list (Z * Z) :=
  [(THIS + 8, THIS + 12); (THIS + 24, THIS + 28); (THIS + 72, THIS + 96); (ASI, ASI + 4 * len + 36);
   (ATP, ATP + ntp); (ASB, ASB + nsb); (AOC, AOC + 8192); (AIA, AIA + 1024)].

Definition parse_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (lo B : Z) (errv : word) (data : list Z)
         (pim psi pcp ptp psb poc pia : bptr) (THIS ASI ACP ATP ASB AOC AIA DOC BUF nim nsi ncp ntp nsb noc nia : Z)
         (x8 x24 x72 x80 x88 : word) (jtp jsb joc jia : list byte),
    let d := strip_bom data in
    RHEAP s LB m ->
    List.NoDup [pim; psi; pcp; ptp; psb; poc; pia] ->
    In (pim, THIS, nim) LB -> 96 <= nim -> In (psi, ASI, nsi) LB -> 4 * zlength d + 36 <= nsi ->
    In (pcp, ACP, ncp) LB -> ACP <= BUF -> BUF + zlength d + 64 <= ACP + ncp ->
    In (ptp, ATP, ntp) LB -> In (psb, ASB, nsb) LB -> In (poc, AOC, noc) LB -> 8192 <= noc -> In (pia, AIA, nia) LB -> 1024 <= nia ->
    ntp mod 8 = 0 -> 8 * (zlength d + 3) <= ntp <= 2^27 -> 5 * zlength d + 182 <= 3 * nsb -> zlength d + 60 <= nsb <= 2^24 ->
    bytes_at psegs m BUF (s1buf d) -> Forall (fun c => 0 <= c < 256) d -> zlength d + 64 <= 2^20 ->
    rw_cells psegs m (THIS + 8) [C4 x8] -> rw_cells psegs m (THIS + 16) [C8 (Z_to_bv 64 ASI)] ->
    rw_cells psegs m (THIS + 24) [C4 x24] ->
    rw_cells psegs m (THIS + 40) [C8 (Z_to_bv 64 MAX_DEPTH); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
    rw_cells psegs m (THIS + 56) [C8 (Z_to_bv 64 AOC); C8 (Z_to_bv 64 AIA); C8 x72; C8 x80; C8 x88] ->
    wr_at psegs m THIS 96 -> wr_at psegs m ASI (4 * zlength d + 36) ->
    rw_cells psegs m DOC [C8 (Z_to_bv 64 ATP); C8 (Z_to_bv 64 ASB)] -> bv_unsigned sp <= DOC -> DOC + 16 <= B -> DOC mod 8 = 0 ->
    rw_cells psegs m ATP [CB (Z.to_nat ntp) jtp] -> rw_cells psegs m ASB [CB (Z.to_nat nsb) jsb] ->
    rw_cells psegs m AOC [CB 8192 joc] -> rw_cells psegs m AIA [CB 1024 jia] ->
    rw_cells psegs m PFMIN fmin_cells -> rw_cells psegs m PGOT_NOTHROW [C8 (Z_to_bv 64 PNOTHROW)] ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PARSE_STACK ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2^47 ->
    rw_cells psegs m (errno_addr tp) [C4 errv] ->
    mem_inv psegs m -> frm0 fc ->
    tp = Z_to_bv 64 RATP ->
    a0 = Z_to_bv 64 THIS -> a1 = Z_to_bv 64 BUF -> a2 = Z_to_bv 64 (zlength d) -> a3 = Z_to_bv 64 DOC ->
    implM psegs (HarnessP.parse_impl raw_malloc raw_free ProgP.new_handler data) s
          (s2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo B
                   (parse_win (bv_unsigned sp) THIS ASI (zlength d) ATP ntp ASB nsb AOC AIA) m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 PPARSE) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Lemma parse_impl_rn : forall data idx, scan (strip_bom data) = (true, idx) ->
  HarnessP.parse_impl raw_malloc raw_free ProgP.new_handler data = rn_copy (strip_bom data) idx.
Proof.
  intros data idx H. unfold HarnessP.parse_impl, HarnessP.root_copy, root_number_alloc, rn_copy. cbv zeta. rewrite H.
  destruct idx as [|i0 r]; [reflexivity|]. unfold zlength. destruct (is_numstart _); reflexivity.
Qed.
Lemma parse_impl_fail : forall data, fst (scan (strip_bom data)) = false ->
  HarnessP.parse_impl raw_malloc raw_free ProgP.new_handler data = mret tt.
Proof.
  intros data H. unfold HarnessP.parse_impl, HarnessP.root_copy, root_number_alloc. cbv zeta.
  destruct (scan (strip_bom data)) as [[|] [|i0 r]]; cbn in H; try discriminate; reflexivity.
Qed.
End CANSEC1.
