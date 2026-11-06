(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/As/AllocWalkKit.v, with its module paths and module names changed; 353 of its 387 lines of code are new or changed and 128 lines of the source are left out. *)
(* Callees of the frame-allocation helper __asan_stack_malloc_{0,1,3} of fuzz_state.asan: the 4-byte jump
   0x42af4 to the __tls_get_addr wrapper (0x47414) and what it calls (TryAsanInitFromRtl 0x5a174, musl
   __tls_get_addr 0x99624, GetCurrentThread 0x5c974 with AsanTSDGet 0x554c0 and pthread_getspecific 0x9a6d8,
   DTLS_on_tls_get_addr 0x6a088), and MemToShadow 0x3dd78. Walk style of the tink-cc tink_encrypt_fuzzer lib/AW
   AFakeLeaf.v, restated with the thread pointer and the thread records as parameters. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.UL Require Import Tac Image ZBridge Arr SysStep.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AK Require Import StepFast StoreFast.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Tk.AK Require Import LiaFix.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_ul.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step_core segs R F pc fc rv m ro ::= step_core_fast segs R F pc fc rv m ro.
Local Ltac zsimp ::= zsimp_fast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* A load reads a cell of a hypothesis whose base is at most 8191 bytes below the address. *)
Ltac solve_load_guard :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 8192)) in
        lazymatch ok with true => idtac end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in
        let ok := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 8192)) in
        lazymatch ok with true => idtac end;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.
Ltac solve_load ::= first [ solve_load_guard | solve_load_image ].

#[local] Abbreviation mem := (word -> option byte).

(* The cells the __tls_get_addr wrapper reads (struct.asan.runtime RT2.5-RT2.6). *)
Definition leaf_cells (TP DT TS C T DB k : Z) (tb te : word) (m : mem) : Prop :=
  ro_cells rsegs m 0xa15d0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (2^64 - 2048))]
  /\ ro_cells rsegs m (TP + -8) [C8 (Z_to_bv 64 DT)]
  /\ ro_cells rsegs m (DT + 8) [C8 (Z_to_bv 64 (TP + 2048))]
  /\ ro_cells rsegs m 0xaa398 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa8f20 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa8f24 [C4 (Z_to_bv 64 k)]
  /\ ro_cells rsegs m (TP + -88) [C8 (Z_to_bv 64 TS)]
  /\ ro_cells rsegs m (TS + 8 * k) [C8 (Z_to_bv 64 C)]
  /\ ro_cells rsegs m (C + 152) [C8 (Z_to_bv 64 T)]
  /\ ro_cells rsegs m (T + 48) [C8 tb; C8 te]
  /\ ro_cells rsegs m 0xa2690 [C8 (Z_to_bv 64 0x99624)]
  /\ ro_cells rsegs m 0xa08e0 [C8 (Z_to_bv 64 0x13b1e8)]
  /\ ro_cells rsegs m 0x13b271 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xa0940 [C8 (Z_to_bv 64 0x139158)]
  /\ ro_cells rsegs m 0x139158 [C4 (Z_to_bv 64 0)]
  /\ ro_cells rsegs m 0xa15e0 [C8 (Z_to_bv 64 8)]
  /\ ro_cells rsegs m (TP + 8) [C8 (Z_to_bv 64 DB)]
  /\ ro_cells rsegs m (DB + 24) [C8 (Z_to_bv 64 TP)]
  /\ (88 <= TP /\ TP + 16 <= 2^64 /\ 0 <= DT /\ DT + 16 <= 2^64 /\ 0 <= k < 2^32
      /\ 0 <= TS /\ TS + 8 * k + 8 <= 2^64 /\ 0 <= C /\ C + 160 <= 2^64 /\ 0 <= T /\ T + 64 <= 2^64
      /\ 0 < DB /\ DB + 32 <= 2^64).

Definition leaf_ivs (TP DT TS C T DB k : Z) : list (Z * Z) :=
  [(TP - 88, TP - 80); (TP - 8, TP + 16); (DT + 8, DT + 16); (TS + 8 * k, TS + 8 * k + 8);
   (C + 152, C + 160); (T + 48, T + 64); (DB + 24, DB + 32)].

(* [lo, hi) holds no cell of leaf_cells: it is above the image and apart from the thread records. *)
Definition leaf_apart (TP DT TS C T DB k lo hi : Z) : Prop :=
  0x5fe000 <= lo /\ lo <= hi /\ hi <= 2^64 /\ disjoint_from (leaf_ivs TP DT TS C T DB k) lo (hi - lo).

Lemma Forall_disj (W : list (Z * Z)) lo hi a n : Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W ->
  a + n <= lo \/ hi <= a -> disjoint_from W a n.
Proof. intros F H. induction F as [|[wl wh] W' Hx F IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

Lemma leaf_cells_munch TP DT TS C T DB k tb te m m' W lo hi :
  leaf_cells TP DT TS C T DB k tb te m -> munch W m m' -> leaf_apart TP DT TS C T DB k lo hi ->
  Forall (fun iv => lo <= fst iv /\ snd iv <= hi) W -> leaf_cells TP DT TS C T DB k tb te m'.
Proof.
  intros LC MU (A0 & A1 & A2 & D) FA. unfold leaf_ivs in D. cbn [disjoint_from] in D.
  destruct D as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _).
  unfold leaf_cells in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try (eapply ro_cells_transport; [eassumption| exact MU| apply (Forall_disj W lo hi); [exact FA|]]).
  all: cbv [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
  all: first [ left; lia
             | destruct D1 as [X|X]; [right|left]; lia
             | destruct D2 as [X|X]; [right|left]; lia
             | destruct D3 as [X|X]; [right|left]; lia
             | destruct D4 as [X|X]; [right|left]; lia
             | destruct D5 as [X|X]; [right|left]; lia
             | destruct D6 as [X|X]; [right|left]; lia
             | destruct D7 as [X|X]; [right|left]; lia ].
Qed.

Lemma leaf_apart_sub TP DT TS C T DB k lo hi lo' hi' :
  leaf_apart TP DT TS C T DB k lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> leaf_apart TP DT TS C T DB k lo' hi'.
Proof.
  intros (A0 & A1 & A2 & D) H1 H2 H3. split; [lia|]. split; [lia|]. split; [lia|].
  unfold leaf_ivs in *. cbn [disjoint_from] in *. repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; lia.
Qed.

Ltac lits H := repeat match type of H with context [Z.add ?a ?b] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (Z.add a b) in change (Z.add a b) with v in H end.
Tactic Notation "leafc" integer(k) hyp(LC) ident(H) := pose proof LC as H; unfold leaf_cells in H; do k (apply proj2 in H);
  lazymatch type of H with _ /\ _ => apply proj1 in H | _ => idtac end; lits H.
Ltac leafr LC := let X := fresh "LR" in pose proof LC as X; unfold leaf_cells in X; do 18 (apply proj2 in X).

Ltac freshLC H :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    match goal with LC : leaf_cells ?a ?b ?c ?d ?e ?f ?g ?h ?i ?m0, MU : munch _ ?m0 mx, AP : leaf_apart _ _ _ _ _ _ _ ?lo ?hi |- _ =>
      pose proof (leaf_cells_munch a b c d e f g h i m0 mx _ lo hi LC MU AP ltac:(repeat constructor; cbn; lia)) as H end end.

(* musl __tls_get_addr (0x99624) for the module-1 descriptor 0xa15d0: returns the thread pointer. *)
Definition tga_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (TP : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma tga_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te,
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leaf_cells TP DT TS C T DB k tb te m -> mem_inv rsegs m ->
  evt rsegs (tga_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc TP m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99624) fc None m (seg_rom rsegs)).
Proof.
  intros until te. intros -> -> LC MI. leafc 0 LC V. leafc 1 LC DTV. leafc 2 LC DTV1. leafr LC.
  do 9 zstep. clear V DTV DTV1.
  match goal with |- context [Z_to_bv 64 (?x + (TP + 2048))] =>
    replace (Z_to_bv 64 (x + (TP + 2048))) with (Z_to_bv 64 TP) by word_eq_tac end.
  apply evt_done. eexists _, _, m. split; [cbv delta [mkR]; reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.

(* TryAsanInitFromRtl (0x5a174) with asan_inited = 1: returns 1. *)
Definition tryinit_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma tryinit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  leaf_cells TP DT TS C T DB k tb te m -> leaf_apart TP DT TS C T DB k (bv_unsigned sp - 16) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs (tryinit_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5a174) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO LC AP MI. leafc 3 LC INI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct AP as (AP0 & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. do 4 zstep.
  zstep. zstep. zstep.
  zstep. if_cases K; zify_cond K; [exfalso; apply K; vm_compute; reflexivity|].
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold tryinit_post.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
Qed.

Lemma sx32_shl32 : forall k, 0 <= k < 2^32 ->
  Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 k))) 32) = Z_to_bv 64 (k * 4294967296).
Proof.
  intros k Hk. apply Z_to_bv_eqm. unfold sx32. rewrite unsigned_lit_wrap, (unsigned_lit k) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Zmult_mod_idemp_l.
  assert (E : bv_swrap 32 k = k \/ bv_swrap 32 k = k - 2^32).
  { destruct (Z_lt_dec k (2^31)); [left; apply swrap32_small; lia| right; rewrite bv_swrap_hi; [unfold bv_modulus; cbn; lia| discriminate| unfold bv_half_modulus, bv_modulus; cbn; lia| unfold bv_modulus; cbn; lia]]. }
  destruct E as [E|E]; rewrite E; [reflexivity|].
  replace ((k - 2^32) * 2^32) with (k * 4294967296 + (-1) * 2^64) by lia. rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma shr29_idx : forall k, 0 <= k -> Z.shiftr (k * 4294967296) 29 = 8 * k.
Proof.
  intros k Hk. rewrite Z.shiftr_div_pow2 by lia.
  replace (k * 4294967296) with ((8 * k) * 2^29) by lia. apply Z_div_mult. lia.
Qed.

(* AsanTSDGet (0x554c0), which jumps to pthread_getspecific (0x9a6d8): returns the key-k slot of the thread's
   table, C. *)
Definition tsdget_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (C : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 C) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma tsdget_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te,
  tp = Z_to_bv 64 TP -> leaf_cells TP DT TS C T DB k tb te m -> mem_inv rsegs m ->
  evt rsegs (tsdget_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc C m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x554c0) fc None m (seg_rom rsegs)).
Proof.
  intros until te. intros -> LC MI. leafc 4 LC KEY. leafc 5 LC TSD. leafc 6 LC TSD0. leafc 7 LC CC. leafr LC.
  do 3 zstep. zstep. if_cases K; zify_cond K; [exfalso; lia|].
  zstep. zstep. zstep. zstep. zstep. rewrite sx32_shl32 by lia. zstep. rewrite shr29_idx by lia.
  zstep. set (Q := TS + 8 * k) in *. clearbody Q. zstep. zstep.
  apply evt_done. eexists _, m. split; [cbv delta [mkR]; reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
Qed.

(* GetCurrentThread (0x5c974): returns 0 when the slot record C is 0, else the thread record T (word 152 of C). *)
Definition thr_of (C T : Z) : Z := if Z.eqb C 0 then 0 else T.

Definition getthread_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (T lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma getthread_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 ->
  tp = Z_to_bv 64 TP -> leaf_cells TP DT TS C T DB k tb te m -> leaf_apart TP DT TS C T DB k (bv_unsigned sp - 16) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  evt rsegs (getthread_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (thr_of C T) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x5c974) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO TPE LC AP MI. leafr LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST. zstep.
  freshLC LC0.
  zstep. call tsdget_spec; [exact TPE| exact LC0| exact MI|]. clear LC0.
  zstep. if_cases K; zify_cond K.
  - do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold getthread_post, thr_of. rewrite K. cbn [Z.eqb].
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
  - freshLC LC1. leafc 8 LC1 THR. clear LC1.
    zstep. do 2 zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply evt_done. unfold getthread_post, thr_of. replace (C =? 0) with false by (symmetry; apply Z.eqb_neq; exact K).
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* DTLS_on_tls_get_addr (0x6a088) with the module-1 descriptor: the thread's DTLS block DB already holds a nonzero
   word at DB + 24, so the function returns 0 after the first lookup. *)
Definition dtls_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma dtls_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 ->
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leaf_cells TP DT TS C T DB k tb te m ->
  leaf_apart TP DT TS C T DB k (bv_unsigned sp - 144) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs (dtls_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x6a088) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO -> -> LC AP MI. leafr LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 144%nat ST. do 13 zstep.
  zstep.
  freshLC LC0. leafc 11 LC0 GCF. leafc 12 LC0 ICF.
  do 3 zstep. clear GCF ICF.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  leafc 13 LC0 GGEN. leafc 0 LC0 DESC. leafc 14 LC0 GEN. leafc 15 LC0 GOFF.
  zstep. do 2 zstep.
  zstep.
  zstep. zstep. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
  zstep. zstep. zstep. clear GGEN DESC GEN GOFF. rewrite (Z.add_comm 8 TP).
  zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
  leafc 16 LC0 DPTR.
  zstep. clear DPTR.
  zstep. zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
  zstep. if_cases K4; zify_cond K4; [| exfalso; lia].
  zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
  clear LC0. zstep. zstep.
  freshLC LC1.
  zstep. zstep. if_cases K6; zify_cond K6; [| exfalso; lia].
  do 3 zstep.
  leafc 17 LC1 DTV1.
  zstep. clear DTV1.
  zstep. if_cases K7; zify_cond K7; [exfalso; lia|].
  zstep. do 13 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
  apply evt_done. unfold dtls_post.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, mx end.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* The 4-byte jump 0x42af4 to the __tls_get_addr wrapper (0x47414), for the module-1 descriptor 0xa15d0: returns the
   thread pointer TP and writes only its 176 stack bytes. *)
Definition icpt_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (TP lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Lemma icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem)
    TP DT TS C T DB k tb te (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 ->
  a0 = Z_to_bv 64 0xa15d0 -> tp = Z_to_bv 64 TP -> leaf_cells TP DT TS C T DB k tb te m ->
  leaf_apart TP DT TS C T DB k (bv_unsigned sp - 176) (bv_unsigned sp) -> mem_inv rsegs m ->
  evt rsegs (icpt_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc TP lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x42af4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros ST LO A0 TPE LC AP MI. leafr LC.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep.
  freshLC LCa.
  zstep. call_sp tryinit_spec; [exact ST| lia| exact LCa| eapply leaf_apart_sub; [exact AP| lia ..]| assumption |].
  rename POST into ST. clear LCa.
  freshLC LC0. leafc 10 LC0 RREAL. do 2 zstep. clear RREAL.
  do 2 zstep.
  zstep. subst a0.
  call tga_spec; [reflexivity| exact TPE| exact LC0| assumption|]. clear LC0.
  zstep.
  zstep. if_cases K; zify_cond K; [exfalso; lia|].
  freshLC LC1.
  zstep. call_sp getthread_spec; [exact ST| lia| exact TPE| exact LC1| eapply leaf_apart_sub; [exact AP| lia ..]| assumption|].
  rename POST into ST. clear LC1.
  assert (TR : 0 <= thr_of C T < 2^64) by (unfold thr_of; destruct (C =? 0); lia).
  zstep. if_cases K2; zify_cond K2.
  - zstep. zstep. do 2 zstep. zstep.
    freshLC LC2.
    call_sp dtls_spec; [exact ST| lia| reflexivity| exact TPE| exact LC2| eapply leaf_apart_sub; [exact AP| lia ..]| assumption|].
    rename POST into ST. clear LC2.
    zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold icpt_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, _, _, mx end.
    split; [subst tp; cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
  - assert (ET : thr_of C T = T) by (unfold thr_of in *; destruct (C =? 0); [lia| reflexivity]).
    rewrite ET in *. freshLC LC2. leafc 9 LC2 TLSB.
    do 2 zstep. clear TLSB. zstep.
    do 2 zstep.
    zstep. call_sp dtls_spec; [exact ST| lia| reflexivity| exact TPE| exact LC2| eapply leaf_apart_sub; [exact AP| lia ..]| assumption|].
    rename POST into ST. clear LC2.
    zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
    apply evt_done. unfold icpt_post.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => eexists _, _, _, mx end.
    split; [subst tp; cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; assumption.
Qed.

(* The cells MemToShadow (0x3dd78) reads on its fast path (struct.asan.runtime RT1): the shadow offset 0x7fff8000
   through its GOT slot, and the high-memory end and the empty middle range through theirs. *)
Definition m2s_cells (m : mem) : Prop :=
  ro_cells rsegs m 0xa08f0 [C8 (Z_to_bv 64 0xa96b8); C8 (Z_to_bv 64 0xaa3a8); C8 (Z_to_bv 64 0xaa3b0); C8 (Z_to_bv 64 0xaa3a0)]
  /\ ro_cells rsegs m 0xa96b8 [C8 (Z_to_bv 64 0x7fff8000)]
  /\ ro_cells rsegs m 0xaa3a0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Lemma Forall_lo_disj (W : list (Z * Z)) lo a n : Forall (fun iv => lo <= fst iv) W -> a + n <= lo -> disjoint_from W a n.
Proof. intros F H. induction F as [|[wl wh] W' Hx F IH]; cbn in *; [exact I|]. split; [lia| exact IH]. Qed.

Lemma m2s_cells_munch m m' W : m2s_cells m -> munch W m m' -> Forall (fun iv => 0x5fe000 <= fst iv) W -> m2s_cells m'.
Proof.
  intros (K1 & K2 & K3) MU FA.
  split; [|split]; (eapply ro_cells_transport; [eassumption| exact MU| apply (Forall_lo_disj W 0x5fe000); [exact FA| cbn; lia]]).
Qed.

Definition m2s_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A / 8 + 0x7fff8000)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma m2s_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (m : mem) (A : Z),
  a0 = Z_to_bv 64 A ->
  (0 <= A < 0x7fff8000) \/ (0x10007fff8000 <= A < 0x800000000000) ->
  m2s_cells m -> mem_inv rsegs m ->
  evt rsegs (m2s_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x3dd78) fc None m (seg_rom rsegs)).
Proof.
  intros until A. intros -> HA (G1 & SB & KH) MI.
  do 3 zstep. clear SB.
  do 4 zstep.
  replace (Z.land ((Z.b2z (2147450880 <? 2147450879) + -1) mod 18446744073709551616) 2147450879) with 2147450879 by reflexivity.
  zstep. if_cases K1; zify_cond K1.
  { destruct HA as [HA|HA]; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].
    do 3 zstep.
    match goal with |- context [Z_to_bv 64 (?x + Z.shiftr A 3)] =>
      replace (x + Z.shiftr A 3) with (A / 8 + 0x7fff8000) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
    apply evt_done. unfold m2s_post.
    eexists _, _, _, _, _, _, _, _, m. split; [cbv delta [mkR]; reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]]. }
  destruct HA as [HA|HA]; [exfalso; revert K1; rewrite ?unsigned_lit by lia; lia|].
  do 4 zstep. zstep. zstep.
  zstep.
  zstep. if_cases K2; zify_cond K2; [| exfalso; revert K2; rewrite ?unsigned_lit by lia; lia].
  do 2 zstep. zstep.
  do 2 zstep.
  zstep. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; lia|].
  zstep. if_cases K4; zify_cond K4; [exfalso; revert K4; rewrite ?unsigned_lit by lia; lia|].
  do 3 zstep.
  match goal with |- context [Z_to_bv 64 (?x + Z.shiftr A 3)] =>
    replace (x + Z.shiftr A 3) with (A / 8 + 0x7fff8000) by (rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia) end.
  apply evt_done. unfold m2s_post.
  eexists _, _, _, _, _, _, _, _, m. split; [cbv delta [mkR]; reflexivity| split; [apply munch_refl| split; [apply wmono_refl| exact MI]]].
Qed.
