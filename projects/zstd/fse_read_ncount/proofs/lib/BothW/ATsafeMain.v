(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import BackingAlgebra MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad STree Stdio Harness Adapter Driver ProgA
AsanCtrl AsanCtrlProps SizeHist AsanEmbed AsanProgDeps AsanInv AsanTotal AsanOK RSimProg AsanHandoffBoth Prog.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg AProto ATsafeCore ATsafeEv ATsafeAlloc ATsafeOps ATsafeProg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition VMAX : Z := MAIN_COST.
Definition WMAX : Z := NOPS.
Definition cls_pages (SB : Z) (c : Z) : list word :=
range_pages (shad (SB + c * K_REGION) - 4096) (UWIN / 8 + 8192)
++ range_pages (shad (SB + c * K_REGION + K_FREEARR_OFF)) (FWIN / 8)
++ map (fun i => Z_to_bv 64 (shad (SB + c * K_REGION) + 32768 * Z.of_nat i)) (seq 0 (Z.to_nat 14337)).
Definition CLS_PAGES : Z := 19975.
Definition win_pages (V : nat -> Z) : list word :=
flat_map (fun c => cls_pages (a_space_beg0 V) (Z.of_nat c)) (seq 1 31)
++ range_pages (shad (a_ptr_array0 V)) (shlen K_PTRARR_RESERVE).
Definition K0 : Z := 600959 + 31 * CLS_PAGES + (2^8 + 2).
Definition NMAXZ : Z := K0 + pcred VMAX WMAX.
Definition NMAX : nat := Z.to_nat NMAXZ.
#[using="Type"] Lemma NMAX_Z : Z.of_nat NMAX = NMAXZ.
Proof. unfold NMAX. apply Z2Nat.id. vm_compute. discriminate. Qed.
Definition Ahand (V : nat -> Z) : alw := fun p => bv_unsigned p mod 4096 = 0 /\ aallowed (allow_of ASHOFF V both_vis) p.
Definition A0 (V : nat -> Z) : alw := aunion (Ahand V) (win_pages V).
#[using="Type"] Theorem A0_init : forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V both_vis) p -> A0 V p.
Proof. intros V p Hal Ha. left. split; assumption. Qed.
#[using="Type"] Lemma HRES : Z.of_nat NMAX * 4096 <= RESERVE34.
Proof. rewrite NMAX_Z. vm_compute. discriminate. Qed.
#[using="Type"] Lemma shlen_vals : shlen K_PTRARR_RESERVE = 2^20 /\ UWIN / 8 + 8192 = 18882560 /\ FWIN / 8 = 4194304.
Proof. repeat split; reflexivity. Qed.
#[using="Type"] Lemma flat_map_length_le : forall {A B} (f : A -> list B) (l : list A) (b : Z),
(forall x, In x l -> Z.of_nat (length (f x)) <= b) -> Z.of_nat (length (flat_map f l)) <= Z.of_nat (length l) * b.
Proof.
intros A B f l b H. Local Ltac2 Set LiaHints.tbl := fun () => "0020>21880564288.1030826702375.6 000007008S2IH2H0S".
induction l as [|x l IH]; cbn [flat_map length]; [lia|]. rewrite length_app, Nat2Z.inj_add, Nat2Z.inj_succ.
specialize (IH ltac:(intros y Hy; apply H; right; exact Hy)). pose proof (H x (or_introl eq_refl)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc"] Lemma shad_cls : forall SB c, SB mod 4096 = 0 -> shad (SB + c * K_REGION) = shad SB + c * 536870912
/\ shad (SB + c * K_REGION + K_FREEARR_OFF) = shad SB + c * 536870912 + 469762048
/\ shad (SB + c * K_REGION + UWIN) = shad SB + c * 536870912 + UWIN / 8
/\ shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN) = shad SB + c * 536870912 + 469762048 + FWIN / 8.
Proof.
intros SB c HSB. rewrite !(shad_div8 0%nat). unfold K_REGION, K_FREEARR_OFF, UWIN, FWIN.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>16414335684.2618928852038.4 4352632486.33 46436947220.2656855281348.3300000E00F00c01801US3HSB2H02H12H52H63H10SS3HSB2H02H12H52H63H103H113H15S3HSB2H02H12H52H63H10S3HSB2H02H12H52H63H103H113H15".
pose proof (Z.div_mod SB 4096 ltac:(lia)). repeat split; Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section V.
Variable V : nat -> Z.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
Local Notation SB := (a_space_beg0 V).
Local Notation PA := (a_ptr_array0 V).
#[using="HP HAT"] Lemma HSB : 0 <= SB /\ SB + K_SPACE_SIZE <= ATOP.
Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_space_beg0, K_SPACE_SIZE, PRIM_SZ, a_usp0 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>58538437694.1200000FS3HAT2H12H22H42H52H61H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HP HAT"] Lemma HPA : 0 <= PA /\ PA + K_PTRARR_RESERVE <= ATOP.
Proof. pose proof (placement_facts V HP) as (H1 & H2 & H3 & H4 & H5 & H6 & H7). unfold a_ptr_array0, K_PTRARR_RESERVE, PTR_SZ, a_usp0 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>57054935039.1200000AS3HAT2H12H32H52H7".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP"] Lemma SB_al : SB mod 4096 = 0.
Proof. pose proof (space_beg0_facts V HP) as (H1 & _). Local Ltac2 Set LiaHints.tbl := fun () => "0030=18926759668.718933043916.736770060565.7000001002003SSS".
apply (Z.mod_divide _ 65536) in H1; [|lia]. destruct H1 as [q Hq]. rewrite Hq.
replace (q * 65536) with ((q * 16) * 4096) by lia. apply Z.mod_mul. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HP"] Lemma PA_al : PA mod 4096 = 0.
Proof. pose proof (space_beg0_facts V HP) as (_ & _ & H & _). exact H. Qed.
#[using="rc"] Lemma A0_cls : forall c p, 1 <= c <= 31 -> In p (cls_pages SB c) -> A0 V p.
Proof.
intros c p Hc Hp. right. unfold win_pages. apply in_or_app. left. apply in_flat_map. exists (Z.to_nat c).
Local Ltac2 Set LiaHints.tbl := fun () => "0020=18930286956.968384130463.9000004008S2HcS2Hc".
split; [apply in_seq; lia|]. rewrite Z2Nat.id by lia. exact Hp.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HAT"] Lemma ABASE_SH : forall z',
((exists c, 1 <= c <= 31 /\
(shad (SB + c * K_REGION) <= z' < shad (SB + c * K_REGION + UWIN)
\/ shad (SB + c * K_REGION + K_FREEARR_OFF) <= z' < shad (SB + c * K_REGION + K_FREEARR_OFF + FWIN)))
\/ shad PA <= z' < shad (PA + K_PTRARR_RESERVE)) -> A0 V (page_base_of z').
Proof.
intros z' Hz. pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as (E1 & E2 & E3).
Local Ltac2 Set LiaHints.tbl := fun () => "0080>13258178577.2355849425584.1455849425584.1564512866271.2365321167894.1665521730585.237904900818.16 7904900818.23 00000=00F00O00\00a00k00o019S3SH12C24Hc29S2S12S21HS2P12P21HS3SH12C14Hc29S3SH2S2Hz2C12C3S2HzS2Hz2C22C4".
pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
destruct Hz as [(c & Hc & Hz)|Hz].
- pose proof (shad_cls SB c SB_al) as (C1 & C2 & C3 & C4).
assert (Hc29 : 0 <= c * 536870912 <= 31 * 536870912) by nia.
apply (A0_cls c); [exact Hc|]. unfold cls_pages. apply in_or_app.
destruct Hz as [Hz|Hz]; [left| right; apply in_or_app; left]; apply range_pages_spec; lia.
- right. unfold win_pages. apply in_or_app. right. apply range_pages_spec; [lia|].
rewrite (shad8 0%nat PA K_PTRARR_RESERVE PA_al) in Hz. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HAT"] Lemma win_pages_length : Z.of_nat (length (win_pages V)) <= 31 * CLS_PAGES + (2^8 + 2).
Proof.
pose proof HSB as [S1 S2]. pose proof HPA as [P1 P2]. pose proof shlen_vals as (E1 & E2 & E3).
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>13258178577.2318672416432.2222137238975.2341094249848.1654783371676.2455849425584.1255849425584.1364512866271.2265321167894.1467792869265.1400000@00G00Q00X00b00k01401D01I01JS3SH12Hx2C24Hc29S2E22HxS2E22E32HxS2LP2LCS2Hx2L12L2S2S12S21HS2P12P21HS3SH12Hx2C14Hc29S3SH2S".
pose proof (shad_bounds 0%nat SB ltac:(unfold K_SPACE_SIZE in *; lia)) as SH1.
pose proof (shad_bounds 0%nat PA ltac:(unfold K_PTRARR_RESERVE in *; lia)) as SH2.
unfold win_pages. rewrite length_app, Nat2Z.inj_add.
pose proof (range_pages_length (shad PA) (shlen K_PTRARR_RESERVE) ltac:(lia) ltac:(rewrite E1; lia)) as LP. rewrite E1 in LP |- *. change (2^20 / 4096) with (2^8) in LP.
assert (LC : Z.of_nat (length (flat_map (fun c => cls_pages SB (Z.of_nat c)) (seq 1 31))) <= 31 * 19975).
{ replace 31 with (Z.of_nat (length (seq 1 31))) at 1 by (rewrite length_seq; reflexivity).
apply flat_map_length_le. intros x Hx. apply in_seq in Hx.
pose proof (shad_cls SB (Z.of_nat x) SB_al) as (C1 & C2 & C3 & C4).
assert (Hc29 : 0 <= Z.of_nat x * 536870912 <= 31 * 536870912) by nia.
unfold cls_pages. rewrite !length_app, length_map, length_seq, !Nat2Z.inj_add. rewrite ?Z2Nat.id by lia.
pose proof (range_pages_length (shad (SB + Z.of_nat x * K_REGION) - 4096) (UWIN / 8 + 8192) ltac:(lia) ltac:(lia)) as L1.
pose proof (range_pages_length (shad (SB + Z.of_nat x * K_REGION + K_FREEARR_OFF)) (FWIN / 8) ltac:(lia) ltac:(lia)) as L2.
rewrite E2 in L1 |- *. rewrite E3 in L2 |- *. change (18882560 / 4096) with 4610 in L1. change (4194304 / 4096) with 1024 in L2. lia. }
unfold CLS_PAGES. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HAT"] Lemma A0_abud_gen : ivz_wf (allow_of ASHOFF V both_vis) -> ivz_bytes (allow_of ASHOFF V both_vis) <= both_abytes -> abud (A0 V) K0.
Proof.
intros HWF AB. unfold A0, K0.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>18930958230.1124338619482.1259138592498.8 00000100:00=SS3HLL3AB'S1H".
apply (abud_mono _ (600959 + Z.of_nat (length (win_pages V)))); [apply abud_union| pose proof win_pages_length; lia].
destruct (aallowed_fin (allow_of ASHOFF V both_vis) HWF) as (L & ND & HLL & HIN).
exists L. split; [exact ND|]. split; [| intros p [Hal Ha]; apply HIN; assumption].
unfold both_abytes in AB. change MainEntryBoth.ASHOFF with ASHOFF in AB.
pose proof (Z.div_le_mono _ _ 4096 ltac:(lia) AB) as AB'. change (2460728320 / 4096) with 600763 in AB'. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HAT"] Lemma A0_abud_L : forall lim sp fs mo, bmodelL lim V sp fs mo -> abud (A0 V) K0.
Proof. intros lim sp fs mo HM. apply A0_abud_gen; [exact (bmL_allow_wf _ _ _ _ _ HM)| exact (bmL_abytes _ _ _ _ _ HM)]. Qed.
End V.
#[using="rc"] Theorem A0_lat : forall V (p : word) (c k : Z), 0 <= a_space_beg0 V -> a_space_beg0 V mod 4096 = 0 ->
bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (a_space_beg0 V) + 536870912 * c + 32768 * k)) -> A0 V p.
Proof.
intros V p c k S0 SAL Hal Hc Hp. pose proof shlen_vals as (E1 & E2 & E3).
pose proof (shad_cls (a_space_beg0 V) c SAL) as (C1 & C2 & C3 & C4).
assert (SH1 : 2147450880 <= shad (a_space_beg0 V)).
{ rewrite (shad_div8 0%nat). Local Ltac2 Set LiaHints.tbl := fun () => "0080>19349091306.181998653020.20 48086560992.1951807186996.2063368135978.1764523340524.1964822087042.207169316620.19 00000300700;00?00@00M00Q00gS1HS2HkS2HcS2HkSS2C13SH14Hc29S2HpS2S02Hp2E22C13SH14Hc29".
pose proof (Z.div_pos (a_space_beg0 V) 8 S0 ltac:(lia)). lia. }
assert (Hc29 : 536870912 <= c * 536870912 <= 31 * 536870912) by nia.
apply (A0_cls V c); [lia|]. unfold cls_pages. apply in_or_app. destruct Hp as [Hp|[Hk Hp]].
- left. rewrite <- (page_base_of_self 0%nat p Hal). apply range_pages_spec; lia.
- right. apply in_or_app. right. apply in_map_iff. exists (Z.to_nat k). split; [| apply in_seq; lia].
rewrite Z2Nat.id by lia. rewrite C1. replace (shad (a_space_beg0 V) + c * 536870912 + 32768 * k) with (bv_unsigned p) by lia. apply Z_to_bv_bv_unsigned.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Main.
Variable V : nat -> Z.
Hypothesis HP : Forall (pfact_ok V) both_pure_facts.
Hypothesis HAT : a_usp0 V - 8388608 = ATOP.
Variable sp : word.
Hypothesis HSP : atop_of sp = ATOP.
Local Notation SB := (a_space_beg0 V).
Local Notation PA := (a_ptr_array0 V).
Definition J : list (AsanCtrl.aptr * Z) -> Z -> Z -> preT (St:=APS) := JJ NMAX SB PA (A0 V).
#[using="Type"] Lemma J_acct : forall Y v w RNG A s mo, J Y v w RNG A s mo -> acct_ok NMAX RNG A mo.
Proof. exact (JJ_acct NMAX SB PA (A0 V) HRES). Qed.
#[using="Type"] Lemma J_perm : forall Y Y' v w RNG A s mo, Permutation Y Y' -> J Y v w RNG A s mo -> J Y' v w RNG A s mo.
Proof. exact (JJ_perm NMAX SB PA (A0 V)). Qed.
#[using="Type"] Lemma J_credit : forall Y v w v' w' RNG A s mo, 0 <= v' <= v -> 0 <= w' <= w -> J Y v w RNG A s mo -> J Y v' w' RNG A s mo.
Proof. exact (JJ_credit NMAX SB PA (A0 V)). Qed.
#[using="Type"] Lemma J_nonneg : forall Y v w RNG A s mo, J Y v w RNG A s mo -> 0 <= v /\ 0 <= w.
Proof. exact (JJ_nonneg NMAX SB PA (A0 V)). Qed.
#[using="HP HAT"] Lemma J_io : forall n Y v w RNG A s mo rsp mo' evs, io_node n -> nstep n mo rsp mo' evs -> J Y v w RNG A s mo -> J Y v w RNG A s mo'.
Proof. exact (JJ_io NMAX SB PA (A0 V) (HSB V HP HAT) (HPA V HP HAT)). Qed.
#[using="Type"] Lemma J_so : forall Y v w RNG A s mo x, J Y v w RNG A s mo -> J Y v w RNG A (aset_so x s) mo.
Proof. exact (JJ_so NMAX SB PA (A0 V)). Qed.
Local Notation TSM := (TSM NMAX (St:=APS)).
#[using="HP HAT"] Lemma Jm : forall Y v w n, 0 <= n <= REQMAX -> HISTOK (n :: map snd Y) ->
TSM (fun RNG A s mo => J Y v w RNG A s mo /\ n <= v /\ 1 <= w) (amalloc_M n)
(fun r RNG A s mo => exists q, r = Some q /\ J ((q, n) :: Y) (v - n) (w - 1) RNG A s mo /\ n < 2^63).
Proof. exact (U_malloc NMAX SB PA (A0 V) HRES (ABASE_SH V HP HAT)). Qed.
#[using="HP HAT"] Lemma Jf : forall Y v w p n, TSM (J ((p, n) :: Y) v w) (afree_M p) (fun _ => J Y v w).
Proof. exact (U_free NMAX SB PA (A0 V) HRES (ABASE_SH V HP HAT)). Qed.
Ltac jx := first [ exact J_acct | exact J_perm | exact J_credit | exact J_nonneg | exact J_io | exact J_so | exact Jm | exact Jf ].
#[using="Type"] Lemma Jnh : forall Y v w (Q : postM (St:=APS) Empty_set), TSM (J Y v w) (new_handlerA AAllocAsan) Q.
Proof. intros Y v w Q. unfold new_handlerA. apply TSM_munr. apply J_acct. Qed.
#[using="HP HAT"] Lemma Jemit : forall Y v w z, TSJ NMAX J Y v w (io_emit (ioA AAllocAsan) z).
Proof. intros Y v w z. cbn [io_emit ioA io_S]. eapply s_emit_ok; jx. Qed.
#[using="HP HAT"] Lemma Jrun : forall X cfg payload v w, (length X <= 1)%nat -> zlength payload <= MAX_INPUT -> RUN_COST <= v -> RUN_OPS <= w ->
TSM (J X v w) (runA AAllocAsan cfg payload) (fun _ => J X (v - RUN_COST) (w - RUN_OPS)).
Proof.
intros X cfg payload v w HX Hp Hv Hw. unfold runA, fuzz_oneA. cbn [amalloc afree AAllocAsan].
eapply target_run_ok; try jx; first [apply Jnh| apply Jemit| exact HX| exact Hp| exact Hv| exact Hw].
Qed.
#[using="HP HAT"] Lemma Jdiag : forall Y v w d, TSJ NMAX J Y v w (io_diag (ioA AAllocAsan) d).
Proof. intros. cbn [io_diag ioA io_S]. eapply s_diag_ok; jx. Qed.
#[using="HP HAT"] Lemma Jioexit : forall Y v w, TSJ NMAX J Y v w (io_exit (ioA AAllocAsan)).
Proof. intros. cbn [io_exit ioA io_S]. eapply stdout_exit_flush_ok; jx. Qed.
#[using="Type"] Lemma Jinit : forall Y v w bm, TSJ NMAX J Y v w (alloc_initA AAllocAsan bm).
Proof. intros. unfold alloc_initA, target_alloc_init. eapply TSJ_ret; jx. Qed.
#[using="Type"] Lemma Jcount : forall Y v w, TSJ NMAX J Y v w (alloc_countA AAllocAsan).
Proof. intros. unfold alloc_countA, target_alloc_count. eapply TSJ_ret; jx. Qed.
#[using="HP HAT"] Lemma progA_main_ok : forall rs argv v w (Q : postM (St:=APS) Empty_set), MAIN_COST <= v -> MAIN_OPS <= w ->
TSM (J [] v w) (progA_main AAllocAsan rs argv) Q.
Proof.
intros rs argv v w Q Hv Hw. unfold progA_main. cbn [amalloc afree aptr_addr AAllocAsan].
eapply main_exit_ok; try jx; first [apply Jdiag| apply Jinit| apply Jcount| apply Jrun| apply Jioexit| exact Hv| exact Hw].
Qed.
#[using="HP HAT HSP"] Lemma J_init_L : forall lim fs mo, LIMIT34 <= lim -> bmodelL lim V sp fs mo ->
J [] VMAX WMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V) (aps_init SB PA (resv_of V) (atop_of sp)) (MX mo []).
Proof.
intros lim fs mo HL HM. destruct (AI_init_L lim V sp fs mo HL HM HP) as (HAI & _).
unfold J, JJ. split; [exact HAI|]. split; [exact HSP|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
Local Ltac2 Set LiaHints.tbl := fun () => "0040>16294883041.1348936900862.1360817585261.136885959932.13 000001002003004SSSS".
split; [unfold VMAX, MAIN_COST, READ_COST, RUN_COST, FUZZ_COST, PRODUCER_SIZE, BUFF_MAX, MAX_INPUT; lia|].
split; [unfold WMAX; cbn [aps_m aps_init a_next ainit Z.of_N]; unfold NOPS; lia|].
exists [], K0. split; [unfold QOK; cbn [aps_m aps_init]; rewrite all_chunks_ainit; constructor|].
split; [apply alw_le_refl|]. split; [apply GA_nil|]. split; [eapply A0_abud_L; [exact HP| exact HAT| exact HM]|].
split; [unfold K0, CLS_PAGES; lia|]. rewrite NMAX_Z. unfold NMAXZ. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HAT HSP"] Theorem progA_tsafe_L : forall lim rs inp mo, LIMIT34 <= lim -> bmodelL lim V sp (in_fs inp) mo ->
tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
(progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof.
intros lim rs inp mo HL HM.
apply (TS_tsafeA NMAX _ _ _ _ (EQ (fun (_ : unit) _ _ _ => True))).
unfold progA_tree. eapply TS_ebind.
- exact (progA_main_ok rs (argv_Z (in_argv inp)) VMAX WMAX (fun _ _ _ _ _ => True) ltac:(unfold VMAX; lia) ltac:(unfold WMAX, NOPS, MAIN_OPS, READ_OPS, RUN_OPS, FUZZ_OPS; lia) _ _ _ _ (J_init_L _ _ _ HL HM)).
- intros [[] s] RNG' A' mo' _ _.
Qed.
#[using="rc HP HAT HSP"] Theorem progA_tsafe : forall rs inp mo, bmodel V sp (in_fs inp) mo ->
tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
(progA_tree AAllocAsan (aps_init SB PA (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof.
intros rs inp mo HM. apply (progA_tsafe_L target_alloc_limit); [| apply bmodel_bmodelL; exact HM].
rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.
End Main.
#[using="Type"] Corollary progA_tsafe_open : forall rs V sp inp mo,
Forall (pfact_ok V) both_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> bmodel V sp (in_fs inp) mo ->
tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
(progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof. intros rs V sp inp mo HP HAT HSP HM. exact (progA_tsafe V HP HAT sp HSP rs inp mo HM). Qed.
#[using="Type"] Corollary progA_tsafe_open_L : forall lim rs V sp inp mo, LIMIT34 <= lim ->
Forall (pfact_ok V) both_pure_facts -> a_usp0 V - 8388608 = ATOP -> atop_of sp = ATOP -> bmodelL lim V sp (in_fs inp) mo ->
tsafeA nstepA (nsafeA NMAX) fstepS NMAX (fp_ok (m_vm_lazy (MX mo [])) (A0 V)) (A0 V)
(progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of sp)) rs (argv_Z (in_argv inp))) (MX mo []).
Proof. intros lim rs V sp inp mo HL HP HAT HSP HM. exact (progA_tsafe_L V HP HAT sp HSP lim rs inp mo HL HM). Qed.
End CANSEC1.
