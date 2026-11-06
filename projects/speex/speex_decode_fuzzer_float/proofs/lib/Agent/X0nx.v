(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd X0pj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0ol X0pd X0qp X0p6 X0p5.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ql X0q1 X0qf X0o1 X0o2 X0oj X0o3 X0o4 X0o7 X0o8 X0o9 X0oa X0ob X0ns X0nt X0nv X0nw X0ny.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Section MMEQ.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> X1qu.M R :=
let size := UNIT * size_class sc in
let st1 := step_seq (account_bounce sc st2) in
fun r =>
if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) nd r) then bad_answer bail else
if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
else
let '(st2, rid) := new_region RKGroup r nd st1 in
let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
let ai := (4096 - UNIT) / size - 1 in
let ai := if c - 1 <? ai then c - 1 else ai in
let ai := if ai <? 0 then 0 else ai in
ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

#[using="Type"] Lemma ag_mmap_eq st2 m cnt :
ag_mmap sc req k bail st2 m cnt =
(let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
(mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
(is_bouncing sc st2) in
SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R).
#[using="Type"] Lemma ag_tail_kq_eq stT mm p c ai :
m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
rewrite as_queue_eq.
2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
unfold as_queue_st. cbn [get_head].
match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
intros H. unfold mm_cnt_red.
destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
Z.div_mod_to_equations. lia.
Qed.

Lemma mm_final_props size req u1 cnt nos c nd :
1 <= cnt <= 32 -> 16 <= size -> 0 <= req -> req + 4 <= size ->
mm_final size req u1 cnt nos = (c, nd) ->
1 <= c <= cnt /\ nd mod 4096 = 0 /\ req + 20 <= nd
/\ (c = 1 /\ nd = round_up_pg (req + 20) \/ size * c + 16 <= nd /\ nd = round_up_pg (size * c + 16)).
Proof.
intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
change (size * cnt + UNIT) with (size * cnt + 16) in E.
destruct (negb nos && (cnt <=? 7)).
- destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
+ inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
+ destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
* inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
* inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
- inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

Lemma pos_iter_slots (m p : aptr) (stride : Z) : forall n tb,
0 < stride ->
let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
fst (Pos.iter F (0, tb) n) = Z.pos n
/\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
/\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
- cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
- rewrite Pos.iter_succ. destruct IH as (I1 & I2 & I3). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
split; [lia|]. split.
+ rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
+ intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
* right. exists (Z.pos n). split; [lia| reflexivity].
* rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first m p stride c st : 1 <= c -> 0 < stride ->
(s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
/\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
destruct (pos_iter_slots m p stride n (s_slots st) HS) as (_ & A & B). split; [exact A| exact B].
Qed.

Definition lowW {RCEIL : RunCeiling} (iv : Z * Z) : Prop :=
0 <= fst iv /\ snd iv <= alloc_ceiling /\ (snd iv <= 0x19000 \/ 0x1b000 <= fst iv \/ (CTX <= fst iv /\ snd iv <= CTX + 928)).

Lemma lowW_meta {RCEIL : RunCeiling} st m' q : mrep st m' -> meta_slot st q -> lowW (conc st q, conc st q + 40).
Proof.
intros MR MS. first [ pose proof (meta_slot_bounds st m' q MR MS) as sfP_; sf_destruct 4%nat sfP_ as Gpos GC GI _ | sf_fb; destruct (meta_slot_bounds st m' q MR MS) as (Gpos & GC & GI & _) ]. unfold lowW, alloc_ceiling. cbn [fst snd]. lia.
Qed.

Definition metaW (st : mstate) (iv : Z * Z) : Prop :=
(exists q, meta_slot st q /\ fst iv = conc st q /\ snd iv = conc st q + 40) \/ iv = (CTX + 16, CTX + 24).

Lemma failW_shape st mt :
meta_slot st mt ->
(forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
Forall (metaW st) (failW st mt).
Proof.
intros MS FL. unfold failW.
constructor; [left; exists mt; auto|].
constructor; [right; reflexivity|].
destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH; [|constructor].
destruct (FL h eq_refl) as [MSh FP].
constructor; [left; exists h; auto|].
destruct (m_prev (get_meta_rec st h)) as [p|] eqn:HP; [|constructor].
constructor; [left; exists p; auto| constructor].
Qed.

Lemma failW_low {RCEIL : RunCeiling} st mt m' :
mrep st m' -> meta_slot st mt ->
(forall h, c_free_meta_head (ctx st) = Some h -> meta_slot st h /\ forall p, m_prev (get_meta_rec st h) = Some p -> meta_slot st p) ->
Forall lowW (failW st mt).
Proof.
intros MR MS FL. eapply Forall_impl; [| exact (failW_shape st mt MS FL)].
intros [lo hi] [(q & MSq & E1 & E2)|E]; [cbn in E1, E2; subst; eapply lowW_meta; eassumption| inversion E; subst; unfold lowW, alloc_ceiling, CTX; cbn; lia].
Qed.

Lemma lowW_disjoint {RCEIL : RunCeiling} W a n : Forall lowW W -> alloc_ceiling <= a -> disjoint_from W a n.
Proof. intros FW Ha. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (H1 & H2 & H3). cbn in *. lia. Qed.

Lemma lowW_disjoint_img {RCEIL : RunCeiling} W a n : Forall lowW W -> 0x19000 <= a -> a + n <= 0x1b000 -> (a + n <= CTX \/ CTX + 928 <= a) -> disjoint_from W a n.
Proof. intros FW H1 H2 H3. eapply Forall_disjoint_from; [exact FW|]. intros lo hi (X1 & X2 & X3). cbn in *. unfold alloc_ceiling in X2. lia. Qed.

Lemma stS_shape sc st2 : exists f, step_seq (account_bounce sc st2) = upd_ctx f st2
/\ forall c, c_active (f c) = c_active c /\ c_usage (f c) = c_usage c /\ c_brk (f c) = c_brk c
/\ c_mmap_counter (f c) = c_mmap_counter c /\ c_free_meta_head (f c) = c_free_meta_head c
/\ c_avail_meta (f c) = c_avail_meta c /\ c_secret (f c) = c_secret c /\ c_init_done (f c) = c_init_done c
/\ c_avail_meta_count (f c) = c_avail_meta_count c /\ c_avail_meta_area_count (f c) = c_avail_meta_area_count c
/\ c_meta_alloc_shift (f c) = c_meta_alloc_shift c /\ c_meta_area_head (f c) = c_meta_area_head c
/\ c_meta_area_tail (f c) = c_meta_area_tail c /\ c_avail_meta_areas (f c) = c_avail_meta_areas c.
Proof.
assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
{ unfold account_bounce, set_bounce.
destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
destruct AB as (g & EG & HG).
rewrite step_seq_eq. rewrite EG.
destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
- exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
- exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
intros c. destruct (HG c) as [E|[v E]]; rewrite E; repeat split; reflexivity.
Qed.

Section LEVEL.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := X0qa.ist_facts_proof st0 LB st AR IS.

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

#[using="RCEIL sc req SC RQ TP"] Lemma errno_lit4 : errno_addr tp = 107900.
Proof. rewrite TP. rewrite unsigned_lit by lia. reflexivity. Qed.

End LEVEL.
