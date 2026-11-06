(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import MM_syscalls StrFun.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes AKit AKit2 AKitQ AModelFacts APrimFacts ASecFacts ASecSlog RT_stubs ARep ARepKit
F_memset F_apoison F_apoison0 F_aalloc3 F_acache3 F_ammap F_ammapz.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
cbn in HP. Local Ltac2 Set LiaHints.tbl := fun () => "0020>56459188277.9 56461269045.1400000400=S2HES2H12H21H".
destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
Local Ltac transport_after_call segs m m' MU WM ::=
let W := lazymatch type of MU with munch ?W _ _ => W end in
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8arr segs m ?A2 ?xs |- _ =>
first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u32arr segs m ?A2 ?xs |- _ =>
first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u64arr segs m ?A2 ?xs |- _ =>
first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : u8ro segs m ?A2 ?xs |- _ =>
first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
| idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
| H : stk segs m ?loq ?hiq |- _ =>
first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
| clear H ]
| H : munch ?Wq ?mq m |- _ =>
first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
| fail 100 "callee footprint not inside caller footprint" ]
| H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
end.
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=
repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let RD := fresh "RD" in
pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
step; clear RD
end.
Local Ltac astore ST8 i :=
lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
let SOK := fresh "SOK" in
pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
step;
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
let S2 := fresh "STATS" in
pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
replace (A + 8 * i)%Z with E in S2 by lia;
clear ST8; store_done; try clear SOK; rename S2 into ST8
end
end.
Section CANSEC1. Context {rc : runConstT}.
Definition large_entry := 0x36c08.
End CANSEC1.
Notation LARGE_STACK := 464 (only parsing).
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
exists k, 0 <= k <= 1 /\ 6254592 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
/\ 2148232704 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>29374267522.2238733649554.2200000E00WS1H2H12A82H02H22H72H8S1H2H12A82H22H72H8".
destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition large_cells (ctx t PA : Z) (m : amem) : Prop :=
rmap_cells m /\ poison_cells m
/\ rw_cells asegs m 0x99768 [C8 (Z_to_bv 64 0x9b620)] /\ rw_cells asegs m 0x9b620 [C8 (Z_to_bv 64 0x192be)]
/\ rw_cells asegs m 0xa1ce0 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xa1ce4 [C4 (Z_to_bv 64 0)]
/\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
/\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)]
/\ rw_cells asegs m 0x9ee58 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)].
#[using="Type"] Lemma large_cells_frame : forall ctx t PA m m' W, large_cells ctx t PA m -> munch W m m' -> wmono asegs m m' ->
AIMG_HI <= ctx ->
Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv))
\/ (0x9ee70 <= fst iv /\ snd iv <= 0xa1680)) W -> large_cells ctx t PA m'.
Proof.
intros ctx t PA m m' W LC MU WM CX HW.
destruct LC as ((Q1 & Q2 & Q3 & Q4 & Q5) & (P1 & P2 & P3 & P4 & P5 & P6 & P7) & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10).
unfold AIMG_HI, AIMG_LO, ATP88, ATSD in *.
assert (D : forall A k, 0 <= k -> ((0x10000 <= A /\ A + k <= 0x9ee70) \/ (0xa1680 <= A /\ A + k <= 0x5f7000) \/ (A = ctx + 152 /\ k = 8)) -> disjoint_from W A k).
{ clear -HW CX. intros A k Hk HA. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion HW; subst. cbn in *. split; [lia| apply IH; assumption]. }
unfold large_cells, rmap_cells, poison_cells. repeat lazymatch goal with |- _ /\ _ => split end;
(eapply rw_cells_transport; [eassumption | exact MU | exact WM | unfold ATP88, ATSD; cbn; apply D; lia]).
Qed.
#[using="Type"] Lemma zeros32_hdr : forall m A, fill_at m A 32 0 ->
rw_cells asegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
Proof. intros m A H. eapply rw_cells_recast; [exact H | cbn; tauto | vm_compute; reflexivity | reflexivity]. Qed.
#[using="Type"] Lemma mtx_to_C4 : forall m (b : Z), 0 <= b < 256 ->
rw_cells asegs m 0x9f0c0 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x9f0c0 [C4 (Z_to_bv 64 b)].
Proof.
intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=38834543651.557022093363.560302399878.5000004005006S2HbSS".
replace b with (b + 256 * 0) at 1 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mtx_of_C4 : forall m (b : Z), 0 <= b < 256 ->
rw_cells asegs m 0x9f0c0 [C4 (Z_to_bv 64 b)] ->
rw_cells asegs m 0x9f0c0 [C1 (Z_to_bv 8 b); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof.
intros m b Hb H. eapply rw_cells_recast; [exact H | cbn; tauto | | reflexivity].
cbn [cells_bytes cbytes app]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=38834543651.557022093363.560302399878.5000004005006S2HbSS".
replace b with (b + 256 * 0) at 2 by lia. rewrite (le4_two_bytes b 0) by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition large_post (RNG : footprint) (sp : word) (a n ctx t PA nres nsec nres' lo : Z) (m : amem)
(RNG' : footprint) (m' : amem) : Prop :=
let size := needed_size n in let ms := sec_map_size n in let res := a + 4096 in let ue := res + size in
fp_le RNG RNG' /\ fp_bw RNG'
/\ a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP
/\ munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
(AINSTANCE + 112, AINSTANCE + 720); (t + 2800, t + 3168);
(PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres')]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec);
CB (Z.to_nat (4096 - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (4096 - 32)))]
/\ rw_cells asegs m' res [CB (Z.to_nat (ms - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms - 4096)))]
/\ fill_at m' (shad a) 512 0xfa
/\ fill_at m' (shad a + 512) (size / 8) 0
/\ fill_at m' (shad a + 512 + size / 8) (ms / 8 - 512 - size / 8) 0xfa
/\ rng RNG' a ms /\ rng RNG' (shad a) (ms / 8)
/\ rw_cells asegs m' 0x9ee88 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
/\ rw_cells asegs m' 0x9ee98 [C1 (Z_to_bv 8 0)]
/\ junk_at m' 0x9eea0 32 /\ junk_at m' 0x9eec0 512
/\ rw_cells asegs m' 0x9f0c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ junk_at m' 0x9f0d8 16
/\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
/\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)]
/\ ((nsec <> nres /\ nres' = nres)
\/ (nsec = nres /\ nres' = nres + 16384
/\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]
/\ rng RNG' (PA + 8 * nres) 131072))
/\ nres' <= 1048576
/\ large_cells ctx t PA m'.
#[using="Type"] Lemma c8x4_of_junk : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
destruct (c8c8_of_junk m A J1) as (w1 & w2 & H1). destruct (c8c8_of_junk m (A + 16) J2) as (w3 & w4 & H2).
exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.
#[using="Type"] Lemma lxor63 : forall k, 0 <= k <= 63 -> Z.lxor k 63 = 63 - k.
Proof.
apply (range_by_compute (fun k => Z.lxor k 63 = 63 - k) (fun k => Z.lxor k 63 =? 63 - k) 0 63); [| vm_compute; reflexivity].
intros z Hz. apply Z.eqb_eq. exact Hz.
Qed.
Definition large_tail_post (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 : word) (F : bvmap 5 word) (fc : bv 32)
(a ms size PA nres' nsec lo : Z) (fj : list byte) (m : amem) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR vra (Z_to_bv 64 sp0) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v t3 t4 t5 t6)
F (ret_pc vra) fc None m' (seg_rom asegs)
/\ munch [(sp0 - 96, sp0); (a + 24, a + 32); (0x9ee88, 0x9f0e8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo sp0
/\ rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)]
/\ rw_cells asegs m' 0x9ee88 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))]
/\ rw_cells asegs m' 0x9ee98 [C1 (Z_to_bv 8 0)]
/\ junk_at m' 0x9eea0 32 /\ junk_at m' 0x9eec0 512
/\ rw_cells asegs m' 0x9f0c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ junk_at m' 0x9f0d8 16
/\ rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
#[using="Type"] Lemma large_tail_spec : forall RNG (sp0 : Z) (vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v : word)
ra gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (a ms size PA nres' nsec k lo : Z) (srt : byte) (fj jstats jbsl jglob jslot : list byte),
stk asegs m lo (sp0 - 96) -> ATOP <= lo -> lo <= sp0 - 96 -> sp0 < 2^64 ->
mem_inv asegs m ->
rw_cells asegs m (sp0 + -96) [CB 8 fj; C8 v9; C8 v8; C8 v7; C8 v6; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
rw_cells asegs m 0x9ee58 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA)] ->
rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0)] ->
rw_cells asegs m 0x9ee88 [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 nsec)] ->
rw_cells asegs m 0x9ee98 [C1 srt] ->
rw_cells asegs m 0x9eea0 [CB 32 jstats] -> rw_cells asegs m 0x9eec0 [CB 512 jbsl] ->
rw_cells asegs m 0x9f0c0 [C4 (Z_to_bv 64 1)] ->
rw_cells asegs m 0x9f0d8 [CB 16 jglob] ->
rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot] ->
ablk a (a + ms) -> a + ms <= ATOP -> (a + ms <= PA \/ PA + 8388608 <= a) ->
ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> 0 <= nsec -> 8 * nsec + 8 <= 8388608 -> 0 <= nres' < 2^64 ->
73728 <= ms <= 536821760 -> 34 <= k <= 47 ->
rng_aimg RNG -> rng RNG lo (sp0 - lo) -> rng RNG a ms -> rng RNG (PA + 8 * nsec) 8 ->
evtF asegs RNG (large_tail_post sp0 vra v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 s10v s11v gp tp a0 F fc a ms size PA nres' nsec lo fj m)
(MS (mkR ra (Z_to_bv 64 (sp0 + -96)) gp tp t0 t1 t2 (Z_to_bv 64 0x9f0c8) (Z_to_bv 64 0x9ee58) a0 a1 a2 (Z_to_bv 64 nsec) a4 a5 a6 a7
(Z_to_bv 64 ms) (Z_to_bv 64 k) s4 (Z_to_bv 64 a) s6 s7 s8 s9 s10v s11v t3 t4 t5 t6)
F (Z_to_bv 64 0x36e6c) fc None m (seg_rom asegs)).
Proof.
intros until jslot. intros ST CEIL LO SP64 MI FR I64 ZH INS SRT JST JBS MTX JGL JSL AHI ACE DAP PA0 PA1 NS0 NS1 NR MSB KB RIMG RSTK RCH RPS.
pose proof AHI as AHI0. pose proof PA0 as PA00. clear AHI PA0. destruct (ablk_int _ _ AHI0) as (kA & AHI & AHIa & AHIb & AHIc & AHId). destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).
atop_facts.
pose proof (munch_refl [(sp0 - 96, sp0); (a + 24, a + 32); (0x9ee88, 0x9f0e8); (PA + 8 * nsec, PA + 8 * nsec + 8)]%Z m) as MU.
pose proof (wmono_refl asegs m) as WM.
box DAP.
destruct (c8_of_junk m (PA + 8 * nsec) (ex_intro _ jslot JSL)) as [wj PAS]. clear JSL.
step.
Local Ltac2 Set LiaHints.tbl := fun () => "00k0?10862073820.11810891020971.1  12053063107.2  12121701742.2  13168802263.16 13584623497.11714507198897.12715342322172.12415342322175.12515675919530.1  18261036110.2  18459507890.10618661153180.1231869417598.0   19438934449.12727050862559.11427445073329.12528768091006.12631000663539.12331153249960.1  31790753535.12533100000457.12334509919194.10835305913430.2  37625410381.12138056291523.12439005674622.12639188636933.0  39263166881.0  39332637397.0  39934446001.12641545695612.1244189464191.125 42061375533.12342974364865.1244377449905.126 44652134833.12645964270975.12547856399731.1175010566057.117 5152994737.125 52078938469.1  54324727969.0  54560324002.11654568455164.12455664284081.1265627157937.125 5627157937.126 56780289891.1  58049312993.4  59796477325.2  61588179377.12562995630236.16 64806989052.12466124323454.12666861428735.12567475915206.11368157851057.1279583930681.1   00000400500900=00L00M00N00R00V00W00X00\00]00^00_00`00a00e00n00o01301401901=01A01B01F01G01H01I01J01N01R01S01T01U01V01Z01[01\01]01^01_01`01d01e01f01g01h01i01m01n02=02A02E02I02R02S02TS2LOSS2KBS2KBS3NS03NS13MSB1YSSS2LOS2LOSSS2KBFSSFSS2LOS2KB4HBSBSS2LOFS3MSBS2KBS2KBSS2LOSSSSS2LOS2LOFSSSS2LOSSSSSSS2LOSSSSSS2KBSS3NS03NS13MSB1YS2LOS2LOS2LOS3NS03NS1SS".
zstep. rewrite (lxor63 k) by (clear -KB; lia).
box PAS. snapshot [(a + 24, a + 32)]%Z MUh WMh.
step.
carry PAS MUh WMh ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUh WMh.
zstep. zstep.
setreg 12 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NS0 NS1; lia).
box ZH. snapshot [(PA + 8 * nsec, PA + 8 * nsec + 8)]%Z MUp WMp.
remember (PA + 8 * nsec) as PS eqn:HPS.
step.
subst PS.
carry ZH MUp WMp ltac:(ub DAP; clear -Y NS0 NS1 AHI AHIa AHIb AHIc AHId MSB; dlia). clear MUp WMp.
destruct (c8x4_of_junk _ 0x9eea0 (ex_intro _ jstats JST)) as (w1 & w2 & w3 & w4 & AST). clear JST.
step. step.
zstep.
step.
zstep. zstep.
step.
step.
step. step.
destruct (junk_split _ 0x9eec0 (8 * (63 - k)) (512 - 8 * (63 - k)) ltac:(replace (8 * (63 - k) + (512 - 8 * (63 - k))) with 512 by (clear; lia); exists jbsl; exact JBS)
ltac:(clear -KB; lia) ltac:(clear -KB; lia)) as [JB1 JB2].
destruct (junk_split _ (0x9eec0 + 8 * (63 - k)) 8 (512 - 8 * (63 - k) - 8) ltac:(replace (8 + (512 - 8 * (63 - k) - 8)) with (512 - 8 * (63 - k)) by (clear; lia); exact JB2)
ltac:(clear; lia) ltac:(clear -KB; lia)) as [JBW JB3]. clear JB2 JBS.
destruct (c8_of_junk _ _ JBW) as [wb BSL]. clear JBW. destruct JB1 as [bs1 JB1]. destruct JB3 as [bs3 JB3].
remember (0x9ee58 + 8 * (63 - k)) as BSB eqn:HBSB.
replace (0x9eec0 + 8 * (63 - k)) with (BSB + 104) in BSL by (subst BSB; clear; lia).
replace (0x9eec0 + 8 * (63 - k) + 8) with (BSB + 112) in JB3 by (subst BSB; clear; lia).
step. if_cases KM; zify_cond KM.
all: try lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x36eb0) _ _ _ _) => step end.
all: zstep; zstep.
all: setreg 11 (Z_to_bv 64 BSB) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); subst BSB; clear -KB; lia).
all: step.
all: zstep.
all: step; step.
all: destruct (c8c8_of_junk _ 0x9f0d8 (ex_intro _ jglob JGL)) as (g0 & g1 & GL); clear JGL.
all: zstep.
all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0x9f0d8) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
all: amo_stepA AMO1.
all: zstep.
all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0x9f0e0) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
all: amo_stepA AMO2.
all: step.
all: apply (mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
all: step.
all: do 13 step.
all: lazymatch goal with FRM : rw_cells asegs ?mm (?spz + -96) (CB 8 _ :: _) |- _ => lazymatch goal with STK : stk asegs mm ?loz _ |- _ => release_frame FRM STK spz end end.
all: apply evtF_done; unfold large_tail_post; do 15 eexists; split; [reflexivity|].
all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [assumption|].
all: split; [exact ZH|]. all: split; [assumption|]. all: split; [assumption|].
all: split; [exact (junk_of_cells _ _ _ AST)|].
all: split.
1,3: subst BSB; replace 512 with (8 * (63 - k) + (512 - 8 * (63 - k))) by (clear; lia);
apply junk_merge; [exists bs1; exact JB1 | | clear -KB; lia| clear -KB; lia];
replace (512 - 8 * (63 - k)) with (8 + (512 - 8 * (63 - k) - 8)) by (clear; lia);
apply junk_merge; [ | | clear; lia | clear -KB; lia];
[ replace (650944 + 8 * (63 - k)) with (650840 + 8 * (63 - k) + 104) by (clear; lia); exact (junk_of_cells _ _ _ BSL)
| replace (650944 + 8 * (63 - k) + 8) with (650840 + 8 * (63 - k) + 112) by (clear; lia); exists bs3; exact JB3 ].
all: split; [assumption|]. all: split; [| assumption].
all: exact (junk_of_cells _ _ _ GL).
Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma large_spec : forall RNG {R} (K : Z -> itree node (exc R)) (K2 : Z -> Z -> itree node (exc R))
(Q : R -> footprint -> machine_state -> Prop) (FRESH : Z -> bool)
ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
(F : bvmap 5 word) fc (m : amem) (n ctx t PA nres nsec lo : Z) (sj : list word) (sorted : Z) (jstats jbsl jglob jslot : list byte),
let size := needed_size n in let ms := sec_map_size n in
stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - LARGE_STACK ->
mem_inv asegs m ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 0x9ee58 -> a1 = Z_to_bv 64 0x9f0c8 -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
1 <= n <= AREQMAX -> is_primary n = false ->
large_cells ctx t PA m ->
sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> t + 4096 <= ATOP -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
rw_cells asegs m 0x9ee88 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
rw_cells asegs m 0x9ee98 [C1 (Z_to_bv 8 sorted)] ->
rw_cells asegs m 0x9eea0 [CB 32 jstats] ->
rw_cells asegs m 0x9eec0 [CB 512 jbsl] ->
rw_cells asegs m 0x9f0c0 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
rw_cells asegs m 0x9f0d8 [CB 16 jglob] ->
ablk PA (PA + 8388608) -> PA + 8388608 <= ATOP -> PA mod 4096 = 0 ->
0 <= nsec <= nres -> nres mod 16384 = 0 -> nres <= 1048576 ->
(nsec < nres -> rw_cells asegs m (PA + 8 * nsec) [CB 8 jslot]) ->
(PA + 8388608 <= t \/ t + 4096 <= PA) -> (PA + 8388608 <= ctx \/ ctx + 4096 <= PA) ->
rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
AIMG_HI <= ctx -> iclr t 4096 ->
(forall a, FRESH a = true ->
ablk a (a + ms)
/\ (a + ms <= t \/ t + 4096 <= a) /\ (a + ms <= ctx \/ ctx + 4096 <= a) /\ (a + ms <= PA \/ PA + 8388608 <= a)
/\ fill_at m (shad a) (ms / 8) 0) ->
(forall a RNG' ms', FRESH a = false -> 0 < a -> a mod 4096 = 0 -> a + ms <= ATOP -> fp_le RNG RNG' ->
implS asegs RNG' (K a) (epostF Q) ms') ->
(forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
FRESH a = true -> nsec <> nres -> large_post RNG sp a n ctx t PA nres nsec nres lo m RNG' m' ->
implS asegs RNG' (K a) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
(forall a, FRESH a = true -> nsec = nres -> nres + 16384 <= 1048576 ->
K a = ebind (enode (NMmap (PA + 8 * nres) 131072 3 50) (adec_mmap ATOP 131072 3)) (K2 a)) ->
(forall a RNG' ms', FRESH a = true -> nsec = nres -> 1048576 < nres + 16384 -> implS asegs RNG' (K a) (epostF Q) ms') ->
(forall a r RNG' ms', r <> PA + 8 * nres -> 0 < r -> r + 131072 <= ATOP -> implS asegs RNG' (K2 a r) (epostF Q) ms') ->
(forall a RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
FRESH a = true -> nsec = nres -> large_post RNG sp a n ctx t PA nres nsec (nres + 16384) lo m RNG' m' ->
implS asegs RNG' (K2 a (PA + 8 * nres)) (epostF Q)
(MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (a + 4096)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs))) ->
implS asegs RNG (ebind (enode (NMmap 0 ms 3 34) (adec_mmap ATOP ms 3)) K) (epostF Q)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 large_entry) fc None m (seg_rom asegs)).
Proof.
intros until jslot. cbv zeta.
intros ST CEIL LO MI TP -> -> -> -> N PRIM LC CX0 CX1 T0 T1 CT2 STATS LSJ INS SRT JST JBS MTX JGL
PA0 PA1 PAL NSR NRM NRB0 JSL DPT DPC RIMG RSTK RCTX RT RPA CXI TIC FROK UNR KONT1 SHAPE2 UNR3 UNR2 KONT2. band_lin.
pose proof PA0 as PA00. clear PA0. destruct (ablk_int _ _ PA00) as (kP & PA0 & PA0a & PA0b & PA0c & PA0d).
pose proof (sec_facts n N PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB).
unfold AIMG_HI, AREQMAX, large_entry in *.
word_range sp SPR.
pose proof (munch_refl [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
set (size := needed_size n) in *. set (ms := sec_map_size n) in *.
box STATS. box INS. box SRT. box JST. box JBS. box MTX. box JGL.
Local Ltac2 Set LiaHints.tbl := fun () => "09F0?10026074842.25210145486483.22 10653515994.2521079682851.231 1081779975.248 10864281461.64 10864281461.65 11051869938.2471149840136.0   11566666413.4  11584862285.17 1162083375.125 11774978335.26411799489570.25211805889266.24711991125079.32 12178473528.54 12289878883.23212291976007.24912322440645.4  12428150072.23112430247196.2481261375960.212 1261375960.260 1261375960.261 1261375962.257 12762956738.17 12870277089.64 12870277089.65 13159172246.5  13313577562.3  13503541744.35 1374799060.20  13892155040.45 13918739985.20 14040914212.25814043218912.24714123482035.31 14256818034.24814618011854.24814620109034.23115038864242.24815041073143.24615041134720.24715041903002.10 15071043833.33 1529805554.247 1538918798.32  15947463047.24915949560227.2321602526669.33  16148322415.24616189233663.18 16261547890.24816548750194.24816804761832.3  16831639642.3  17126407619.52 17126407619.53 17151130279.12717210349934.2  17318890361.55 17318890361.56 17511488259.24917535855693.17 17538010112.24817542202648.24717559379343.18 17594417445.15 17669060082.2471773310350.26  17776320431.12517807136772.2461785468898.3   17986879152.10 17986879152.15 17986879152.20 17986879152.26 17995455655.12618422146077.20 18548796306.23218746109210.25218802973426.24718827493826.33 18913870613.6  18918200149.24718930958230.20 19015967474.24719092398759.1261937063194.15  19617313304.11 19617313304.15 19617313304.24 19617313304.27 19617313304.35 19670594045.24719885335399.10 19885335399.52 19885335399.53 19954217394.24519970277031.12620163737475.12520269398461.55 20269398461.56 20414752114.2482047665247.64  2047665247.65  2050035067.260 21227682692.33 2124193155.126 21284799705.25 21284799705.26 2132597781.37  2132597781.38  21405716698.25221472669832.8  21498922368.17 22024771290.25222195977465.33 22214604530.24722428323719.24822430420899.23122634910938.25222664701128.4  22706555394.6  2295126554.4   23004255682.17 23386168314.18 23627005501.32 23770140939.3  2400638038.22  24207993306.25224347998194.24724436996044.3  24880865951.2  24972242010.25225073974703.24825073974703.24925076071819.23125076071819.23225080282415.24725080282415.24825081078602.32 25318376386.33 25332040434.2472546492594.268 25527905671.24925530002851.23225878270254.12626428819072.17 26502771472.24726502771472.24826685873759.24626730776422.15 27280736896.17 27462345696.26327574660128.25227776532267.2  28370640551.12528450832218.2  28521666290.24728536163186.24829067115679.19 2913425300.25  2913425300.26  2937190991.27  29784318686.2  30008181843.10 30076295366.14 30747847929.33 30768641574.11 30781110002.24730805812953.25 30805812953.26 30824734578.24831012612437.0  31026020490.37 31026020490.38 3104568653.17  31191324469.4  31215926497.52 31215926497.53 31649644204.5  31770941499.52 31770941499.53 31853783632.24831865172116.26131872282082.3  31929422313.14031936348496.5  31937008256.17 32005092028.22 32008254371.23132010351495.24832127996803.12632310233831.37 32310233831.38 32772311962.25232938500103.55 32938500103.56 32958331632.11 33062543571.20 33062543571.26 33406675186.24733493658562.17 33611023395.23133613120519.24833623804571.17 33839637041.24833858867479.0  33890036527.12534029725987.23234031823111.24934164772537.6  34169364217.24734326450181.3  34330730127.10 3457088893.248 34885248674.26835099623002.25235105138947.4  35115460349.26 35205357699.12635209714819.12635257205954.17 35340120754.26635357590978.17 35637039136.21235740462322.24735897425114.25235998161932.22 35998161932.37 35998161932.38 36115622446.12636180999398.11736379156110.7  36457478898.24736515951322.25236651720741.20 36704994663.10 36848298211.23136850395335.24836988760154.25237121590815.52 37121590815.53 37141335815.24837143432995.23137201839402.52 37201839402.53 37390010528.29 3795062108.2   3799266425.1   3804798932.259 3804798932.260 38217320306.24838311247097.33 3832836837.11  38498908914.24738604560519.24938606657699.23238692635477.0  38903098019.23138905195143.24838965490467.1  38968257667.52 38972444991.73 39012636437.0  39170548780.10 39188636933.0  39332637397.0  39362753536.17 39378986105.26439661661252.4  40084807026.20 40091925676.12440150930599.12640336511696.27 40600263088.3  40832288750.26840834385893.26740834385896.26440922097010.24841131622649.33 41270082071.37 41270082071.38 41272171651.12741408184389.26741408184390.26641408184392.26441410281550.26841476191879.2  41526574044.20641536595426.10 41779239794.24842132986300.32 42158217626.17 42248457998.7  42250564277.21342250564277.23042250564277.24742362512680.54 42368801556.47 4237141073.27  4259745615.25  4259745615.26  42669345218.17 42803642915.24842805740039.23142887904618.12 429452623.25   429452623.26   43061792653.11543308111674.3  43358680699.4  4339538087.127 4346516850.248 43467924127.4  43624396838.37 43624396838.38 43786047718.18 43786047718.19 43843024033.0  43987951406.12644007240616.26444009337774.268440101998.1    44487020397.25244572497956.5  44611301484.3  45241786759.24845243883939.2314537170882.33  45486878294.35 45491065834.63 45656729165.25 45656729165.26 45980917854.5  46084819894.26 46219515605.1  46327287962.25246481087529.24746485146729.6  46721790727.24846723887907.23146806235213.17 46932921792.33 46953039917.24747077701064.24747085737157.2344721740417.34  4721740417.38  47314073472.17 47971134322.24848049670002.24848321848473.63 48366989682.24848422387328.17 48492828898.52 48492828898.53 48688118565.10 48721597440.26448721597453.26748723694598.26848729649807.25348729650694.13048956220434.45 49081353231.26349082866238.19 49089206181.2574923662446.6   49421114917.2  49425192486.15 49486495821.25 49486495821.26 49669356060.37 49669356060.38 49819069809.20 4989810034.248 49930925938.24850108362994.24750131542183.12550189134306.7  50218211418.25250330077073.20 50379078919.24850379078919.24950381176099.23150381176099.23250516153480.0  50586667242.54 50600290453.52 50600290453.53 50951108008.55 50951108008.56 50991898330.2525114850435.127 51343512192.17 51361981810.24851517989270.22851561310307.23251563407431.24951678667180.12451789176154.25251862169588.24652074235542.21052254642906.25252523015483.26352575291859.24752575291859.24852877258371.3  52978530989.24853021079846.74 53028877591.4  53070891135.52 53070891135.53 53158413250.17 53184632406.26253223416603.33 53257845651.20 53322291235.23153324388359.24853479616128.17 53508216722.21053663649664.17 53703070450.24753767577775.12553926293342.25 53926293342.26 54110583096.8  54142741234.2475434128321.37  5434128321.38  54455947213.17 54922574194.24855613693426.24755790763809.0  56170256219.21256170256219.22956170256219.24656174447011.7  56230154605.32 56765693369.24656765693885.19856771238972.21256773336117.2095703377594.20  57284206464.17 57628698627.11 57628698627.6  57628698627.8  57699555840.10 57701672254.24757701672383.24657709577267.23457709577278.20657885813324.24858025198450.24858143249301.2  58197755271.24858199852451.23158477402019.23258479499143.2495867961120.37  5867961120.38  58795386246.64 58795386246.65 59048690994.3  59050652417.11 5909425485.17  59192637571.12459308628179.8  59308629082.4  59314873579.11 59314873579.8  59338540786.24759384361202.24759586081466.26659588178609.14259610308480.17 59723945897.22 59825920688.24759847502578.24760141267698.24760189069269.11 60759099917.7  61208149259.3  6124323778.33  61305990311.12461560206755.23261562303879.24961917199023.12562083673382.22 62128165194.18 62128165194.19 62232972069.20 62232972069.26 62250799188.23062252498992.4  62302209411.1266253736030.55  6253736030.56  62885933440.4  62892351972.23063049147592.23063063700652.4  63068058720.64 63068058720.65 63235321900.12363348234032.24863375992104.26463378089262.26863842107213.17 63922752810.23063937043790.6  64022359336.38 64342530482.26864562172029.17 64634307010.33 64674898864.3  64772824451.12564869492058.14 64873932761.44 64953050503.24864955147683.23165095166637.22 65106454934.13065128844401.26 65483078362.25265507993774.26865510090920.26465566963629.1  66110519514.25266149329551.26 66151427842.16 66260595083.6  66280880474.25266336522568.6  66833676748.34 66833676748.38 67105517212.24967381608175.19 6744704702.268 67466105445.2576746801845.267 6746801847.265 6746801848.264 67475915204.26867530006898.24867567392795.4  67680999037.14067800019075.12767802609044.25 67802609044.26 67818022492.25767820119639.26067920000384.17 6798355636.18  6798355636.19  68035828615.24968037925795.23268254437966.20 68254437966.37 68254437966.38 68354050849.0  68354196418.33 7130566823.126 7203867998.25  7203867998.26  7260813424.6   7379503706.252 7484103457.0   7486304935.127 7489617266.248 7583570169.33  7611240667.7   7654287582.264 7850740698.252 8027395954.248 8265267294.0   8558944706.33  8595948977.142 8806422860.11  8806422860.12  8806422860.13  8806422860.8   8806422860.9   8825073913.33  883891058.248  8935173664.270 8935173666.268 8937270825.267 8937270827.265 9197910491.6   9471306659.232 9473403783.249 9638965854.247 9829218171.261 9896718738.11  00000?00L00[00n01T02H03<03E03F03G03R03V03W03o04804G04m05@05f05g05h05i06806G06V06e07007V08<08E08F08h09009S09W09X09Y09m0:60:e0;P0;Y0;^0;c0;h0<20<;0<<0<b0=50=60=;0=@0=I0=R0=W0=X0=Y0=Z0=[0=\0>?0>b0?P0?[0?`0?e0?j0?n0@70@?0@C0@D0@I0@O0@U0@[0@a0@b0A90A[0Aj0B30B>0B?0B@0BA0BJ0BK0BO0BP0BQ0BR0BS0BT0B`0Bo0D60E=0E>0E?0E@0En0F\0Fe0G[0HQ0HV0Hd0He0I70II0IN0IS0Ib0Ic0Ii0J80JB0JK0K10KD0KS0KT0KX0K]0Kh0L20LA0LF0L[0Lj0M30M80M90MH0Nd0OJ0PO0Q90Q:0Q;0QM0QX0Qa0Qb0RH0R[0R_0Re0Rf0Rg0Rl0S10S70S<0S=0S>0S?0S@0SI0SR0SW0S]0Sc0T60T70T80TC0TM0TP0TY0Tk0U=0UF0UG0Uf0VE0VP0VQ0VR0VS0Va0Vb0Vc0Vd0Ve0Vj0W80WA0WG0WY0Wl0XR0XS0Xm0YG0YV0Z40ZR0ZY0ZZ0Z[0Zd0Zo0[B0[h0\60\70\80\<0\O0]50]60]70]<0]A0]M0]N0]]0]^0^=0^>0^?0^J0^K0^V0^e0^n0_=0_I0_U0_a0_e0_f0_g0`00`?0`C0`M0``0aF0aU0aV0aW0b=0bP0bQ0bR0bh0bi0bj0bo0c00c90cC0cI0cR0d80dK0dL0d_0eE0eF0eG0eH0eI0eS0eT0eU0e[0e\0ea0em0f10f20fF0fK0fL0fM0fN0fW0fa0g@0g_0g`0ga0gb0gc0gd0gi0h80hF0hO0ha0hn0i=0iO0ia0j30j40j50jN0jO0jP0j[0j\0j]0jk0jl0jm0k10k20k80k90kB0kJ0k[0kl0l10l60l70l;0l<0l=0l>0l?0l@0lA0lg0m:0mE0mZ0mo0n>0nM0nU0nZ0n[0nj0o>0o?0oe10810C10U10b11311D11V11n12412=12F13<13E13K13L13M13Q13V13[13`13e13j14R14\14f15015115615;15J15Y16016G16S16\16e16n16o17017?17@17f18L18_19219319a19i1:11:_1;M1;\1;]1;c1;l1;m1<@1<f1<j1=91=:1=;1=J1=K1=L1=M1=T1=a1>h1>o1?01?11?<1?A1?V1?W1?j1@P1@V1@W1@]1@f1@j1A91AH1AI1AR1AW1A\1A]1Af1Ao1B01B51B:1B?1B@1BJ1BY1Bh1C71CF1CP1CV1C^1Cb1Cj1D;1DW1E31EO1Ek1El1F51F61F\1Fo1GB1Gh1HB1H\1Hk1I:1I?1IH1IS1IT1I\1Id1J31J:1JC1JL1JM1JN1JT1JW1J]1Jf1Jo1K91K:1K?1KJ1KK1K^1LD1LH1LT1LX1L\1L`1Ld1Le1Lf1Lg1Ll1M11M21M31M41M51Mi1NW1N[1Na1Nb1Nc1Nn1O>1O?1OR1OS1O`1Ok1P01P11P71P81P^1Q11Q41QB1QC1QR1QS1QT1QU1Qd1R51RD1RE1RT1RU1R_1Ri1Rj1S61S71S@1SA1SB1SC1SL1SU1SV1SW1SX1S^1Sd1Se1Sj1T01T31T=1Tc1U61UI1U\1Uo1V01V;1V<1VK1VZ1V[1Vj1Vk1Vl1W51W?1WJ1WO1W^1Wg1Wh1X31X41X<1XH1XP1XT1XX1Xb1Xk1Xl1Xm1Xn1Xo1Y01YC1Yi1Yn1Z31ZAS4CEIL2LO1H3HspS4CEIL2LO3CX1S4CEIL2LO1H3HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3LSJ3TICSSS4CEIL2LO1HS2LOSS4CEIL2LO3CX13Hsp2T13LSJS3LSJ3TICS3NSR3MSB3CWF1YS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSFFS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS4CEIL2LO1HS4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S4CEIL2LO3MSR3SZ83SH21Y1H2H42H52H93H14S3NSR3NSBFS3NSR4PA0b4PA0c3MSB3CWF3SH13SH22LTS3AAL2A0S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S2A0SSS3MSR3MSB3SZ81Y1H2H9S3LSJ3TICS4CEIL2LO3LSJ3MSB2A04AHId3SZP3SH54ASDa4ASDb3HspS4CEIL2LO3LSJ3MSB2A04AHId3SZP4ASDa4ASDb3HspS3LSJ3TICS3LSJS3LSJS3MSBS3NSR4PA0aS3LSJ3TICSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspSS3LSJS3CWFS3LSJ3TICS3LSJ3TICS3HspFFFSSS4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3MSR3MSB3SH21H2H02H42H52H9S4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23SH53HspS4CEIL2LO1HS3LSJS3LSJS3NSRS2LOS3LSJ3TICS4AHId1HS2LOSS3MSBS4CEILS4CEILS4CEILS4CEILSS3MSB4AHIb4AHIc3SH13SH2S4CEIL2LO3LSJ3MSB2A01H3SZP3SH23HspS4CEIL2LO1H3HspS3LSJ3TICS4CEIL2LO1HFFSS3LSJ3TICSS2T1FFFFFS4CEIL2LO2T1S4CEIL2LO3CX11HS4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0S4CEIL2LO3CX11H3SH13SH25CBNDa5CBNDb3TIC2Y13NSR3CXI4PA0a3MSB4AHIa3CWF2Y0SSSS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3LSJ3TICS3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3MSR3MSB4AHIb4AHIc3SZ83SH13SH24ASDa4ASDb1Y1H2H42H52H9S3LSJS3NSR3CWF2LT1YSS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdS3SH1S3SH1S4CEIL2LO1H3HspFS4AHIaS4CEIL2LO1H3HspS3NSR4PA0aS3LSJ3TICS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3HspSS2HqS3MSBS4CEIL2LO1HS3NSR4NRB0S3NSR3MSB3CWF1YS3HspS4CEIL2LO4PA0d3CWF2LTS4CEIL2LO1H3HspS3LSJ3TICS3HspSS4CEIL2LO1H3HspS4CEIL2LO3LSJ2NB3RSR3NSE3MSR3MSB2A01H3SZ83SZP3SH23SH53Hsp3CX13SH15CBNDa5CBNDb2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSB2A01H3SZP3SH23SH53HspS4CEIL2LO3CX13LSJ3MSB2A03SZP3SH13SH25CBNDa5CBNDb3Hsp1H2T15TBNDa5TBNDbS4CEIL2LO3LSJ3MSR3MSB2A01H3SZ83SZP3SH23HspSSS4CEIL2LO4PA0d3CWFS4CEIL2LO1HS3LSJ3TICSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS2LOS4AHIaSSS3LSJS3CX1S4AHIaS3MSBFSSSS3LSJ3TICS3LSJ3TICS3NSRS4AHIaS4AHIaS4CEIL2LO3MSB3SH21HSSS3NSB1Y1E1HS3NSR4PA0aS1HS3LSJ3TICS4CEIL2LO3MSB4AHIdS4CEIL2LO3MSB4AHIdS3LSJ3TICSS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS4CEIL2LO1HFFFS3NSR4NRB03NSBFFSSS3MSBS1N2NB3RSR3NSES3MSR3MSBS4AHIaS4CEIL2LO3MSB4AHIdS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0S4CEIL2LO1H3HspS3MSR3MSB4ASDa4ASDb1H2H02H42H5S3MSR3MSB4ASDa4ASDb1H2H02H42H5S3MSM1HSSS3LSJ3TICS4CEIL2LO1HS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO4AHIdSSS2LOS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspFFS3MSBS3MSBS4CEIL2LO2T1FS4CEIL2LO1H3HspFS3MSB3AAL2A04AHIa3SZ83SZP3MSR1YSSS4CEIL2LO1HSS4CEIL2LO1HS3MSB2A04AHId1HS3LSJ3TICS4CEIL2LO1H3HspS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S2LOSFS3LSJ3TICS4CEIL2LO1H3HspS2LOS3MSB1H2H0S4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3HspSSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspFFS3MSR3SZ81Y1H2H02H42H9SSS3LSJSS3LSJ3TICS3NSR4PA0aS4AHIaS3LSJ3TICS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspSFFSS3SZP1H2H0SSS4AHIaSS3SZPS4PA0d3CWF1HS2LOSS3AAL3SZ81H2H02H42H9S3HspSSSS3LSJ3TICS3NSR4PA0aS3NSR4PA0b4PA0c3MSB3SH13SH23CWFS3NSR4PA0b4PA0c3MSB3SH13SH23CWFSSSSSS3TICS3MSB2A04AHId1HS3MSB2A03ACE1HS3LSJ3TICS4CEIL2LO3MSB4AHIdS3AAL1H2H02H4S4CEIL2LO3SPR1HS4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0S4CEIL2LO3SPR1H2H0FFS3MSB3SH13SH25TBNDa5TBNDbSSS4CEIL2LO1HFFS4CEIL2LO2AH1HSSS2LOSS2T11HSS3LSJ3TICS3NSR2KQS4PA0a3MSB4AHIa1YS4PA0a3MSB4AHIa1YS3SPRS3SPRSS2LOSSSFFSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1HS4CEIL2LO4PA0d3CWF2LTS4CEIL2LO4PA0d3CWF2LTS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS3NSR2KQS3MSRSS4CEIL2LO1H3HspS3LSJ3MSB2A03SZP3SH5FS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1HS4CEIL2LO4PA0d3CWFS5TBNDa5TBNDbS3MSB4AHIa4AHId1HS3MSB4AHIa4AHId1HS3NSR3MSB2KQ3CWF1YS3NSR4PA0a3MSB3CWF2LT2Y0S4AHIaS3LSJ3TICS3LSJ3TICS3NSR4PA0b4PA0c3MSR3MSB3CWF3SZ83SH13SH23SH52LT1Y2H42H9S3LSJ3TICS4AHIaFFS2LOS3MSBS3MSBS3MSBS3MSBS3MSBS3MSR3MSB3SH13SH25TBNDa5TBNDb1H2H02H42H5S3NSR4NRB0S3NSR4NRB0S3NSR4NRB0SS3CXIS3CXIS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YS3MSB4AHIb4AHIc3SH13SH2S3MSB4AHIb4AHIc3SH13SH2S3MSB4AHId1HS3LSJ3TICS3LSJ3TICS3LSJ3TICSSS4CEIL2LO1H3HspSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3SH13HspSS3MSR3MSB3SZ83SH13SH25TBNDa5TBNDb1Y1H2H42H52H9S4AHIa1YS4AHIa1YS3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S3NSR4PA0b4PA0c3MSR3MSB3SH13SH23CWF1H2H02H42H5S4CEIL2LO1H3HspSS4AHIaS3LSJ3TICSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS2LOS4CEIL2LO1H3HspSFS4CEIL2LO1H3HspSSSS1N3RSRS5TBNDa5TBNDbS3AAL4AHIa4AHId3SZ81Y1H2H02H42H52H93H103H143H153H193H243H253H293H343H39S3CX11HFFS4CEIL2LO1HS3MSBS4CEIL2LO4PA0d3CWF2LTSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4AHIaSS4AHIaS3LSJ3TICS2LOS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YFS3LSJ3TICS3TICS3TICSS3LSJ3TICS3LSJ3TICSS3HspS3HspS3HspSS3NSR4PA0aS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3MSB2A04AHId1HS3NSR4PA0aS4AHIaS3CWF2HqS2HqS3CWF2HqS2K02A03ACE3SZP1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HS2NB3RSR3NSE3MSR4AHIa4AHId1HSS3LSJ3TICSS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3NSR4PA0a3MSB4AHIa3CWF2Y0S3NSR4PA0a3MSB4AHIa3CWF2Y0S3SZ83SZP3SH11HS3SZ83SZP3SH11HS3CWFS3NSB1Y1HS4CEIL2LO1HSS3MSR2K0S3MSB2K7S3SZP2K53MSR2K6S2A02K1S3LSJ3TICS3LSJ3TICSSS4AHIaS1YS2T11HS3LSJ3TICS3LSJ3TICS3MSB1H2H0FS3HspS4CEIL2LO1HSS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS2LOS3MSB4AHIa1YS2LOS2LOS2LOS2LOSSSS3SH1S3SH1FFFFS3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H42H52H9S3NSR4PA0b4PA0c3MSR3MSB3SZ83SH13SH23CWF1Y1H2H9S2LOS2T11HSSS4CEIL2LO1HS3LSJ3MSB2A03SZPFS3NSR4PA0a3CWF2LT1YSS3AAL1H2H02H4S4CEIL2LO1HS3HspSS4NRB0FS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS1YS1N2NB3RSR3NSESS4CEIL2LO1H3HspSSSS4CEIL2LO1H3HspS1Y2Y01H2H02H42H9S1Y1H2H02H43AALFS4CEIL2LO1H3HspFS3NSR4PA0aS3NSR4PA0aSS3NSR2KQ3CWFSS3NSR3NSBSSSS3NSR3NSBS3LSJ3TICFFSS4AHIaS4AHIaSS3LSJS4AHIaS1YS3NSR2KQ1YS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS4CEIL2LO1H3SH13HspS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HS4CEIL2LO3MSB3SH21HSS4CEIL2LO1HSS3NSR3MSB3CWF1YS3NSR3MSB3CWF1YFS4CEIL2LO1H3HspSSS3LSJ3TICS3NSR4PA0aS4CEIL2LO1HS3MSBS4CEIL2LO1H3HspS3LSJ3TICSS4CEIL2LO1HSS3CWF2HqS3MSB3CWF2HqS3MSB2HqS2HqS2HqS3NSR4PA0aS3LSJ3TICFFFFFS4CEIL2LO1H3SH13HspS4CEIL2LO3LSJ3MSB2A01H3SZP3SH13SH53HspS3SH5S3LSJS3NSR3NSB1H2H0".
assert (MS4 : exists q, ms = 4096 * q) by (exists (ms / 4096); clear -MSM MSB; Z.div_mod_to_equations; lia).
clear RSE. box MSE. box RSM. box MSM. box NRM. box PAL. box CT2. box DPT. box DPC.
iprefix.
carve_frame 96%nat ST.
do 12 step.
assert (HWL : Forall (fun iv => ((snd iv <= AIMG_LO \/ AIMG_HI <= fst iv) /\ (snd iv <= ctx + 152 \/ ctx + 160 <= fst iv)) \/ (0x9ee70 <= fst iv /\ snd iv <= 0xa1680))
[(bv_unsigned sp - LARGE_STACK, bv_unsigned sp)]%Z)
by (apply Forall_cons; [cbn; left; unfold AIMG_HI, AIMG_LO; clear -SPR CEIL LO CX1 CXI; lia | apply Forall_nil]).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (large_cells_frame ctx t PA m mm _ LC MU WM ltac:(exact CXI) HWL) as LC1 end.
destruct LC1 as (RC & PC & GNM & NAME & TI & TK & T88 & TSD & CT & I64). unfold ATP88, ATSD in *.
step. zstep. zstep. step. if_lit.
step. step.
zstep. zstep. step. if_lit.
step.
zstep. zstep. zstep. zstep.
setreg 11 (Z_to_bv 64 (ms - 4096)) ltac:(rewrite land_align4096 by (clear -MSB MSR; lia); f_equal; unbox MSE; rewrite MSE; clear -MSB; Z.div_mod_to_equations; lia).
zstep. zstep. zstep. zstep. zstep.
change (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0.
setreg 18 (Z_to_bv 64 ms) ltac:(f_equal; clear; lia).
step. if_cases K0; zify_cond K0. 2: { exfalso. clear -K0 MSR MSB NSE RSR N. subst size. lia. }
step.
step. step. step.
step.
step.
apply evtF_done.
lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (mmapz_spec RNG K Q FRESH _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm ms lo) end.
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); exact ST
| |- mem_inv _ _ => assumption
| |- rmap_cells _ => exact RC
| |- rng_aimg _ => exact RIMG
| |- @eq word _ _ => reflexivity
| |- _ mod 4096 = 0 => unboxed MSM
| |- bv_unsigned _ <> 0 => rewrite unsigned_lit by (clear; lia); clear; lia
| |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
end.
all: try (atop_facts; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO MSB; lia).
{
intros a HFR A0 ACE. destruct (FROK a HFR) as (AH & _). unfold ablk, KLS, AIMG_HI in *. rewrite unsigned_lit by (clear -SPR CEIL LO; lia). clear -AH ACE CEIL LO SPR. lia. }
{
intros a RNG' ms' HFR A0 AAL ACE LE. eapply UNR; eassumption. }
intros a RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HFR PO.
destruct PO as (FPLE & BW & AAL & A0 & ACE & MU2 & WM2 & MI2 & ST2 & ZCH & RCH & RSCH & RC2).
destruct (FROK a HFR) as (AHI & DAT & DAC & DAP & SH0). box DAT. box DAC. box DAP.
pose proof AHI as AHI0. clear AHI. destruct (ablk_int _ _ AHI0) as (kA & AHI & AHIa & AHIb & AHIc & AHId).
rewrite unsigned_lit in MU2, ST2 by (clear -SPR CEIL LO; lia).
destruct (Z_lt_le_dec nsec 1048576) as [NSB|NSB].
2: { eapply UNR3; [exact HFR | clear -NSB NSR NRB0; lia | clear -NSB NSR NRB0; lia]. }
set (CW := if nsec =? nres then 131072 else 0).
assert (ECW : CW = (if nsec =? nres then 131072 else 0)) by reflexivity.
assert (CWF : 0 <= CW <= 131072 /\ 8 * nres + CW <= 8388608).
{ rewrite ECW. ub NRM. destruct (Z.eqb_spec nsec nres) as [E|E]; clear -NSB NSR NRB0 Y E; Z.div_mod_to_equations; lia. }
clearbody CW. box ECW.
atop_facts.
assert (SZ8 : size mod 8 = 0) by (rewrite NSE; ub RSM; clear -Y; Z.div_mod_to_equations; lia).
assert (SZP : 0 < size) by (rewrite NSE; clear -RSR N; lia).
assert (SHR : 0x800b6e00 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000 /\ shlen ms = ms / 8 /\ shlen 4096 = 512
/\ shad (a + 4096 + size) = shad a + 512 + size / 8 /\ shlen (ms - 4096 - size) = ms / 8 - 512 - size / 8).
{ unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. ub MSM. clear -AHI AHIa AHIb AHIc AHId ACE MSB AAL SZ8 K0 Y. Z.div_mod_to_equations. lia. }
destruct SHR as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). rewrite SH3 in RSCH.
destruct (ablk_shad_int _ _ AHI0 ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) as (kS & ASD & ASDa & ASDb & _ & _).
destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(clear -T1; lia)) as (kT & TBND & TBNDa & TBNDb). destruct (sclr_int _ _ CX0 ltac:(clear -CXI; lia) ltac:(clear -CX1; lia)) as (kC & CBND & CBNDa & CBNDb).
assert (MU02 : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp + -96); (a, a + ms)]%Z m0 m2)
by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia).
assert (MUA : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms)]%Z m m2).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; clear; intros q Hq; lia. }
assert (WMA : wmono asegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
clear MU WM MU2.
xport FR MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
xport I64 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
xport GNM MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport NAME MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
xport TI MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TK MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
xport T88 MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia). xport TSD MU02 WM2 ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
xport CT MU02 WM2 ltac:(ub DAC; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 Y CXI; dlia).
assert (PC2 : poison_cells m2).
{ eapply poison_cells_frame; [exact PC | exact MU02 | exact WM2 |]. unfold AIMG_HI.
apply Forall_cons; [cbn; clear -SPR CEIL LO; lia|]. apply Forall_cons; [cbn; clear -AHI AHIa AHIb AHIc AHId; lia| apply Forall_nil]. }
clear PC RC ST.
unfold fill_at in SH0. xport SH0 MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE SH1 SH2 MSB; dlia).
unbox STATS. xport STATS MUA WMA ltac:(ub DAT; rewrite LSJ; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE T0 T1 Y TIC; dlia).
unbox INS. xport INS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
unbox SRT. xport SRT MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
unbox JST. xport JST MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
unbox JBS. xport JBS MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
unbox MTX. xport MTX MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
unbox JGL. xport JGL MUA WMA ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE; dlia).
assert (JSL2 : nsec < nres -> rw_cells asegs m2 (PA + 8 * nsec) [CB 8 jslot]).
{ intros LT. specialize (JSL LT). xport JSL MUA WMA ltac:(ub DAP; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT Y; dlia). exact JSL. }
clear JSL.
change (rw_cells asegs m2 (shad a) [CB (Z.to_nat (ms / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (ms / 8)))]) with (fill_at m2 (shad a) (ms / 8) 0) in SH0.
destruct (fill_split m2 (shad a) 512 (ms / 8 - 512) 0 ltac:(replace (512 + (ms / 8 - 512)) with (ms / 8) by (clear; lia); exact SH0) ltac:(clear; lia) ltac:(clear -MSB; Z.div_mod_to_equations; lia))
as [SHH SHR0].
destruct (fill_split m2 (shad a + 512) (size / 8) (ms / 8 - 512 - size / 8) 0 ltac:(replace (size / 8 + (ms / 8 - 512 - size / 8)) with (ms / 8 - 512) by (clear; lia); exact SHR0)
ltac:(clear -SZP; Z.div_mod_to_equations; lia) ltac:(ub MSM; clear -MSB K0 SZ8 Y MSR; Z.div_mod_to_equations; lia))
as [SHU SHT]. clear SHR0.
clear SH0.
apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RCTX.
apply (rng_fp_le _ _ _ _ FPLE) in RT. apply (rng_fp_le _ _ _ _ FPLE) in RPA.
iprefix.
replace (ret_pc (Z_to_bv 64 224452)) with (Z_to_bv 64 224452 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
step. if_cases K1; zify_cond K1. { exfalso. clear -K1 A0 ACE. lia. }
step. step.
zstep. zstep.
setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite (Z.land_comm 4095 a); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; symmetry; exact AAL).
step. if_lit.
zstep. zstep. zstep.
setreg 11 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
zstep. zstep. zstep. zstep. zstep.
change ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) with 0. change (Z.land 0 8) with 0.
setreg 25 (Z_to_bv 64 (a + 4096)) ltac:(f_equal; clear; lia).
zstep. zstep. zstep. zstep.
setreg 23 (Z_to_bv 64 (a + 4096 + size))
ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 SZP; lia);
change (2^3) with 8; clear -AAL SZ8 A0; Z.div_mod_to_equations; lia).
setreg 10 (Z_to_bv 64 (a + 4096))
ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -A0 ACE K0 MSB; lia);
change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
zstep. step. step.
setreg 11 (Z_to_bv 64 4096) ltac:(f_equal; clear; lia).
clear MU02.
apply (munch_weaken _ [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
(0x9ee88, 0x9f0e8); (t + 2800, t + 3168);
(PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z) in MUA.
2: { unfold sub_fp. cbn [outside]. clear. intros q Hq. tauto. }
unfold fill_at in SHH, SHU, SHT.
pose proof PC2 as PCx. destruct PCx as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
pose proof RC2 as RCx. destruct RCx as (Q1 & Q2 & Q3 & Q4 & Q5). clear PC2 RC2 Q3.
Local Ltac pcells := unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption.
assert (RSH1 : rng RNG' (shad a) 512) by (eapply rng_sub'; [exact RSCH|]; clear -MSB; Z.div_mod_to_equations; lia).
pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad a, shad a + 512)]%Z m2) as MUS. pose proof (wmono_refl asegs m2) as WMS.
step. call_sp (poison_shadow_spec_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a 4096 512 250 lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- poison_cells _ => pcells
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ (shad _) _ => exact SHH
| |- rng _ (shad _) _ => exact RSH1
| |- rng_aimg _ => exact RIMG
| |- shlen _ = _ => exact SH4
| |- rng _ _ _ => solve_rng
end.
all: try (eapply ablk_sub; [exact AHI0 | clear; lia | clear -MSB; lia]).
all: try (atop_facts; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB SPR CEIL LO; first [lia | Z.div_mod_to_equations; lia]).
lazymatch goal with M : munch _ m2 ?mm, W : wmono asegs m2 _ |- _ =>
assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 MSB; dlia); exact JSL2);
clear JSL2 M W; rename JSL3 into JSL2 end.
zstep. step. step.
setreg 11 (Z_to_bv 64 (ms - 4096 - size)) ltac:(f_equal; clear; lia).
assert (RSH2 : rng RNG' (shad (a + 4096 + size)) (ms / 8 - 512 - size / 8))
by (rewrite SH5; eapply rng_sub'; [exact RSCH|]; ub MSM; clear -MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; lia).
rewrite <- SH5 in SHT.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (munch_refl [(bv_unsigned sp + -96 - 64, bv_unsigned sp + -96); (shad (a + 4096 + size), shad (a + 4096 + size) + (ms / 8 - 512 - size / 8))]%Z mm) as MUS;
pose proof (wmono_refl asegs mm) as WMS end.
step. call_sp (poison_shadow_spec0_k RNG' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096 + size) (ms - 4096 - size) (ms / 8 - 512 - size / 8) 250 lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- poison_cells _ => pcells
| |- @eq word _ _ => reflexivity
| |- rw_cells _ _ (shad _) _ => exact SHT
| |- rng _ (shad _) _ => exact RSH2
| |- rng_aimg _ => exact RIMG
| |- shlen _ = _ => exact SH6
| |- rng _ _ _ => solve_rng
end.
all: try (eapply ablk_sub; [exact AHI0 | clear -SZP; lia | clear; lia]).
all: try (atop_facts; ub MSM; clear -AAL A0 AHI AHIa AHIb AHIc AHId ACE MSB MSR SPR CEIL LO SZ8 SZP K0 Y; first [lia | Z.div_mod_to_equations; lia]).
lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(ub MSM; clear -SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT SH1 SH2 SH5 MSB MSR SZP SZ8 K0 Y; Z.div_mod_to_equations; dlia); exact JSL2);
clear JSL2 M W; rename JSL3 into JSL2 end.
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (munch_refl [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96)]%Z mm) as MUS; pose proof (wmono_refl asegs mm) as WMS end.
pose proof CT as CT0. box CT0. box ZCH. box POST. box POST0. box SHU.
step. call_sp (thread_stats_spec RNG' ctx t lo).
all: try lazymatch goal with
| |- evtF _ _ _ _ => idtac
| |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption
| |- stk _ _ _ _ => eassumption
| |- mem_inv _ _ => assumption
| |- @eq word _ _ => first [reflexivity | exact TP]
| |- rw_cells _ _ _ _ => assumption
| |- rng_aimg _ => exact RIMG
| |- rng _ _ _ => solve_rng
end.
all: try (unfold AIMG_HI; clear -CEIL LO CX0 CX1 T0 T1 SPR CXI TIC; lia).
lazymatch goal with M : munch _ ?mo ?mm, W : wmono asegs ?mo _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
by (intros LT; specialize (JSL2 LT); xport JSL2 M W ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT; dlia); exact JSL2);
clear JSL2; rename JSL3 into JSL2;
apply (munch_weaken _ [(bv_unsigned sp + -96 - 32, bv_unsigned sp + -96); (t + 2872, t + 2888)]%Z) in M;
[ rename M into MUS2; rename W into WMS2 | unfold sub_fp; cbn [outside]; clear; intros q Hq; tauto ] end.
clear CT.
snapshot [(t + 2872, t + 2888); (a, a + 32); (0x9f0c0, 0x9f0c4)]%Z MUz WMz.
aload STATS 9 (t + 2800 + 72).
aload STATS 10 (t + 2800 + 80).
zstep.
setreg 14 (Z_to_bv 64 0) ltac:(f_equal; change 7 with (Z.ones 3); rewrite Z.land_ones by (clear -A0; lia); change (2^3) with 8; clear -AAL A0; Z.div_mod_to_equations; lia).
zstep. zstep.
astore STATS 9.
astore STATS 10.
carry ZCH MUS2 WMS2 ltac:(ub DAT; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB T1 TIC; dlia).
carry POST MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 T1 TBND TBNDa TBNDb; dlia).
carry SHU MUS2 WMS2 ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
carry POST0 MUS2 WMS2 ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 SZP SZ8 K0 T1 TBND TBNDa TBNDb; Z.div_mod_to_equations; dlia).
clear MUS2 WMS2.
step. if_lit.
step. step.
zstep. zstep.
setreg 12 (Z_to_bv 64 0) ltac:(f_equal; try rewrite (Z.land_comm 4095); change 4095 with (Z.ones 12); rewrite Z.land_ones by (clear -A0; lia); change (2^12) with 4096; clear -AAL A0; Z.div_mod_to_equations; lia).
step. if_lit.
step. if_cases K5; zify_cond K5. { exfalso. clear -K5 A0 SZP ACE MSR. lia. }
step. if_cases K6; zify_cond K6. { exfalso. clear -K6 A0 SZP ACE MSR. lia. }
zstep.
setreg 21 (Z_to_bv 64 a) ltac:(f_equal; clear; lia).
lazymatch type of ZCH with rw_cells _ ?mq _ _ =>
change (fill_at mq a ms 0) in ZCH;
destruct (fill_split mq a 32 (ms - 32) 0 ltac:(replace (32 + (ms - 32)) with ms by (clear; lia); exact ZCH) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZH ZR];
destruct (fill_split mq (a + 32) (4096 - 32) (ms - 4096) 0 ltac:(replace (4096 - 32 + (ms - 4096)) with (ms - 32) by (clear; lia); exact ZR) ltac:(clear; lia) ltac:(clear -MSB; lia)) as [ZP ZU]
end.
clear ZCH ZR. apply zeros32_hdr in ZH. unfold fill_at in ZP, ZU. replace (a + 32 + (4096 - 32)) with (a + 4096) in ZU by (clear; lia).
lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
assert (JSL3 : nsec < nres -> rw_cells asegs mm (PA + 8 * nsec) [CB 8 jslot])
by (intros LT; specialize (JSL2 LT); xport JSL2 MUz WMz ltac:(ub DPT; ub DAP; clear -Y Y0 SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF LT T1 AHI AHIa AHIb AHIc AHId ACE MSB TIC; dlia); exact JSL2);
clear JSL2 MUz WMz; rename JSL3 into JSL2 end.
box STATS. box ZP. box ZU. box POST. box POST0. box SHU.
snapshot [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + 32); (0x9ee88, 0x9f0e8);
(PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z MUr WMr.
snapshot [(a, a + 32); (0x9f0c0, 0x9f0c4)]%Z MUq WMq.
step. step. step.
step. if_cases K7; zify_cond K7. { exfalso. clear -K7 MSB. lia. }
zstep. step. zstep. step.
apply (mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
assert (AMO : amo_aligned AW (Z_to_bv 64 651456) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
amo_stepA AMO.
step. zstep. zstep. zstep.
amo_stepA AMO.
step. if_lit.
zstep. step. if_lit.
step.
zstep.
setreg 11 (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by (clear; lia); clear -NSR NSB; Z.div_mod_to_equations; lia).
step. if_lit.
pose proof (slog_facts ms MSB ltac:(ub MSM; exact Y)) as [CSR CLZ].
do 25 zstep. setreg 11 (Z_to_bv 64 (cb_sm ms)) ltac:(reflexivity).
do 7 zstep. step. do 9 zstep.
setreg 19 (Z_to_bv 64 (cb_clz (cb_sm ms))) ltac:(reflexivity).
step. if_cases KQ; zify_cond KQ.
-
clear MUq WMq JSL2. subst nsec.
assert (NRB : nres + 16384 <= 1048576) by (ub NRM; clear -NSB Y NSR; Z.div_mod_to_equations; lia).
assert (ECW1 : CW = 131072) by (ub ECW; rewrite Z.eqb_refl in Y; exact Y).
clear CWF. assert (CWF : CW = 131072 /\ nres + 16384 <= 1048576) by (split; [exact ECW1| exact NRB]).
step.
zstep. zstep. zstep.
setreg 11 (Z_to_bv 64 (PA + 8 * nres)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -NSR; lia).
step. step. step. step.
step.
apply evtF_done. rewrite (SHAPE2 a HFR eq_refl NRB).
lazymatch goal with |- implS _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
eapply (rmapd_spec RNG' (K2 a) Q _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (PA + 8 * nres) 131072 lo) end.
all: try lazymatch goal with
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eassumption
| |- mem_inv _ _ => assumption
| |- rmap_cells _ => unfold rmap_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end); assumption
| |- rng_aimg _ => exact RIMG
| |- @eq word _ _ => reflexivity
| |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub'; [exact RSTK|]; clear -SPR CEIL LO; lia
| |- (_ + 8 * _) mod 4096 = 0 => ub NRM; ub PAL; clear -Y Y0 NSR; Z.div_mod_to_equations; lia
end.
all: try (unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPR CEIL LO; lia); clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF; lia).
{ intros r RNG'' ms' NE R0 RCE. eapply UNR2; [exact NE | exact R0 | exact RCE]. }
intros RNG'' mc q0 q1 q2 b1 b2 b3 b4 b5 b6 b7 q3 q4 q5 q6 PM.
destruct PM as (FPLE2 & PCE & MUc & WMc & MIc & STc & ZC & RPC & RSPC & BW2 & RCc).
rewrite unsigned_lit in MUc, STc by (clear -SPR CEIL LO; lia).
xport FR MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport I64 MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport INS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport SRT MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport JST MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport JBS MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport MTX MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport JGL MUc WMc ltac:(clear -SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB SH1 SH2; dlia).
xport ZH MUc WMc ltac:(ub DAP; clear -Y SPR CEIL LO PA0 PA0a PA0b PA0c PA0d PA1 NSR NRB0 CWF AHI AHIa AHIb AHIc AHId ACE MSB; dlia).
lazymatch type of MUr with munch ?Wr ?ma ?mb =>
assert (MUr2 : munch Wr ma mc) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
assert (WMr2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMr | exact WMc]) end.
clear MUr WMr. rename MUr2 into MUr. rename WMr2 into WMr.
lazymatch type of MUA with munch ?Wa ?ma ?mb =>
assert (MUA2 : munch Wa ma mc) by (eapply munch_trans; [exact MUA | eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
assert (WMA2 : wmono asegs ma mc) by (eapply wmono_trans; [exact WMA | exact WMc]) end.
clear MUA WMA MUc WMc. rename MUA2 into MUA. rename WMA2 into WMA.
apply (rng_fp_le _ _ _ _ FPLE2) in RIMG. apply (rng_fp_le _ _ _ _ FPLE2) in RSTK. apply (rng_fp_le _ _ _ _ FPLE2) in RCH.
apply (rng_fp_le _ _ _ _ FPLE2) in RSCH. apply (rng_fp_le _ _ _ _ FPLE2) in RPA.
iprefix.
replace (ret_pc (Z_to_bv 64 225380)) with (Z_to_bv 64 225380 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
step.
step. step.
step. zstep.
step.
step.
lazymatch type of ZC with rw_cells _ ?mq _ _ =>
change (fill_at mq (PA + 8 * nres) 131072 0) in ZC;
destruct (fill_split mq (PA + 8 * nres) 8 (131072 - 8) 0 ZC ltac:(clear; lia) ltac:(clear; lia)) as [ZC8 ZCR] end.
clear ZC. unfold fill_at in ZC8, ZCR.
assert (RPS : rng RNG'' (PA + 8 * nres) 8) by (eapply rng_sub'; [exact RPC|]; clear; lia).
eapply evtF_cut.
{ eapply (large_tail_spec RNG'' (bv_unsigned sp)); try eassumption.
all: try reflexivity.
all: try (ub DAP; atop_facts; clear -Y CEIL LO SPR NSR NRB0 CWF PCE; lia). }
cbv beta. intros ms9 PT. unfold large_tail_post in PT.
destruct PT as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & ZH9 & INS9 & SRT9 & JST9 & JBS9 & MTX9 & JGL9 & PAS9).
apply evtF_done. rewrite Z_to_bv_bv_unsigned.
lazymatch type of MUr with munch ?Wr ?ma ?mb =>
assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).
carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
xport ZCR MU9 WM9 ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1; dlia).
assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
(0x9ee88, 0x9f0e8); (t + 2800, t + 3168);
(PA + 8 * nres, PA + 8 * nres + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
{ eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
eapply (KONT2 a RNG'' m9); [exact HFR | reflexivity |].
unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
split; [eapply fp_le_trans; [exact FPLE| exact FPLE2]|]. split; [exact BW2|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nres)] [CB _ _])).
split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
split; [exact ZU|].
split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
split; [exact RCH|]. split; [exact RSCH|].
split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
split; [exact PAS9|].
split; [right; split; [reflexivity|]; split; [reflexivity|]; split; [exact ZCR| exact RPC]|].
split; [clear -CWF; lia|].
eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.
repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
-
assert (ECW0 : CW = 0) by (ub ECW; destruct (Z.eqb_spec nsec nres) as [E|E]; [exfalso; exact (KQ E) | exact Y]).
clear CWF. assert (CWF : CW = 0 /\ nres <= 1048576) by (split; [exact ECW0| exact NRB0]).
specialize (JSL2 ltac:(clear -KQ NSR; lia)).
xport JSL2 MUq WMq ltac:(ub DAP; clear -Y SPR CEIL LO NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d PA1 AHI AHIa AHIb AHIc AHId ACE MSB KQ; dlia). clear MUq WMq.
assert (RPS : rng RNG' (PA + 8 * nsec) 8) by (eapply rng_sub'; [exact RPA|]; clear -KQ NSR; lia).
eapply evtF_cut.
{ eapply (large_tail_spec RNG' (bv_unsigned sp)); try eassumption.
all: try reflexivity.
all: try (ub DAP; clear -Y CEIL LO SPR NSR NRB0 CWF KQ; lia). }
cbv beta. intros ms9 PT. unfold large_tail_post in PT.
destruct PT as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m9 & -> & MU9 & WM9 & MI9 & ST9 & ZH9 & INS9 & SRT9 & JST9 & JBS9 & MTX9 & JGL9 & PAS9).
apply evtF_done. rewrite Z_to_bv_bv_unsigned.
lazymatch type of MUr with munch ?Wr ?ma ?mb =>
assert (MUr9 : munch Wr ma m9) by (eapply munch_trans; [exact MUr | eapply munch_weaken; [| exact MU9]; unfold sub_fp; cbn [outside]; clear -CWF; intros q Hq; lia]);
assert (WMr9 : wmono asegs ma m9) by (eapply wmono_trans; [exact WMr | exact WM9]) end.
clear MUr WMr. rename MUr9 into MUr. rename WMr9 into WMr.
carry ZP MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
carry ZU MUr WMr ltac:(ub DAP; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF; dlia).
carry STATS MUr WMr ltac:(ub DAT; ub DPT; rewrite ?upd_length, ?LSJ; clear -Y Y0 SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB NSR NRB0 CWF T0 T1 PA0 PA0a PA0b PA0c PA0d PA1 TIC; dlia).
carry POST MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d ASD ASDa ASDb; dlia).
carry SHU MUr WMr ltac:(clear -SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
carry POST0 MUr WMr ltac:(rewrite SH5; ub MSM; clear -Y SPR CEIL LO ACE AHI AHIa AHIb AHIc AHId MSB MSR SH1 SH2 SH4 NSR NRB0 CWF PA0 PA0a PA0b PA0c PA0d SZP SZ8 K0 ASD ASDa ASDb; Z.div_mod_to_equations; dlia).
assert (MUF : munch [(bv_unsigned sp - LARGE_STACK, bv_unsigned sp); (a, a + ms); (shad a, shad a + ms / 8);
(0x9ee88, 0x9f0e8); (t + 2800, t + 3168);
(PA + 8 * nsec, PA + 8 * nsec + 8); (PA + 8 * nres, PA + 8 * nres + CW)]%Z m m9).
{ eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU9]. unfold sub_fp. cbn [outside]. clear -MSB CWF. intros q Hq. lia. }
assert (WMF : wmono asegs m m9) by (eapply wmono_trans; [exact WMA | exact WM9]).
eapply (KONT1 a RNG' m9); [exact HFR | exact KQ |].
unfold large_post. cbv zeta. change (needed_size n) with size. change (sec_map_size n) with ms.
split; [exact FPLE|]. split; [exact BW|]. split; [exact AAL|]. split; [exact AHI0|]. split; [atop_facts; exact ACE|].
split; [eapply munch_weaken; [| exact MUF]; unfold sub_fp, AINSTANCE; cbn [outside]; clear -CWF; intros q Hq; lia|]. split; [exact WMF|]. split; [exact MI9|]. split; [exact ST9|].
split. { apply (proj2 (rw_cells_app asegs m9 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 nsec)] [CB _ _])).
split; [exact ZH9|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. exact ZP. }
split; [exact ZU|].
split; [exact POST|]. split; [exact SHU|]. split; [unfold fill_at; rewrite <- SH5; exact POST0|].
split; [exact RCH|]. split; [exact RSCH|].
split; [exact INS9|]. split; [exact SRT9|]. split; [exact JST9|]. split; [exact JBS9|]. split; [exact MTX9|]. split; [exact JGL9|].
split; [eexists; split; [exact STATS| rewrite !upd_length; exact LSJ]|].
split; [exact PAS9|].
split; [left; split; [exact KQ| reflexivity]|].
split; [exact NRB0|].
eapply (large_cells_frame ctx t PA m m9); [exact LC | exact MUF | exact WMF | exact CXI |].
ub DAC. ub DPC. ub CT2. unfold AIMG_HI, AIMG_LO. clear -Y Y0 Y1 SPR CEIL LO AHI AHIa AHIb AHIc AHId ACE CX0 CX1 PA0 PA0a PA0b PA0c PA0d PA1 SH1 SH2 MSB T0 T1 NSR NRB0 CWF CXI TIC CBND CBNDa CBNDb TBND TBNDa TBNDb.
repeat (apply Forall_cons; [cbn [fst snd]; first [right; lia | left; lia] |]). apply Forall_nil.
Unshelve. all: try (apply ref_ro_addr_false; right; lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
