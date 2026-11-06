(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Export Decode.
Import ListNotations.
Open Scope bv_scope.
Lemma evt_ecall : forall segs (Q : machine_state -> Prop) R F pc fc rv m ro w,
fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = true ->
Q (MSsvc R F (Z_to_bv 64 pc) (reg_get R 17) fc rv m ro) ->
evt segs Q (MS R F (Z_to_bv 64 pc) fc rv m ro).
Proof.
intros segs Q R F pc fc rv m ro w Hf He HQ.
eapply evt_step; [|apply evt_done; exact HQ].
split; [reflexivity|]. rewrite (step_ecall_gen segs R F (Z_to_bv 64 pc) fc rv m ro w Hf He). reflexivity.
Qed.
Ltac step_ecall :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with
| Some ?w =>
apply (evt_ecall segs Q R F pc fc rv m ro w);
[ vm_compute; reflexivity | vm_compute; reflexivity | simp_regs ]
| None => fail "no instruction at" pc
end
end.
Lemma nret_MSsvc : forall R F pc x8 fc rv m ro r ws zs us ci,
nret (MSsvc R F pc x8 fc rv m ro) (mkEffectU r ws zs us [] ci)
= MS (bvmap_set 10 r R) F (pc + Z_to_bv 64 4) fc rv (apply_writes (apply_zeros (apply_unmaps m us) zs) ws) ro.
Proof. reflexivity. Qed.
Lemma mkR_set_a0 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 v,
bvmap_set 10 v (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
= mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
Proof. reflexivity. Qed.
Lemma apply_mem_none : forall m, apply_writes (apply_zeros (apply_unmaps m []) []) [] = m.
Proof. reflexivity. Qed.
Lemma apply_mem_write : forall m a bs, apply_writes (apply_zeros (apply_unmaps m []) []) [(a, bs)] = write_to_mem m a bs.
Proof. reflexivity. Qed.
Lemma apply_mem_delivered : forall m a bs,
apply_writes (apply_zeros (apply_unmaps m []) []) (delivered_writes a bs) = write_to_mem m a bs.
Proof. intros m a [|b bs]; reflexivity. Qed.
Definition in_range (a n : Z) (x : word) : bool :=
(a <=? bv_unsigned x)%Z && (bv_unsigned x <? a + n)%Z.
Lemma apply_zeros_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_zeros m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then Some (Z_to_bv 8 0) else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_zeros zeros_cover existsb fst snd]. unfold in_range.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=56763570144.761931854156.7000004008S2HaS2Hn".
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma apply_unmaps_spec : forall m a n x, (0 <= a < 2^64)%Z -> (0 <= n < 2^64)%Z -> (a + n <= 2^64)%Z ->
apply_unmaps m [(wa a, Z_to_bv 64 n)] x = if in_range a n x then None else m x.
Proof.
intros m a n x Ha Hn Han. cbn [apply_unmaps zeros_cover existsb fst snd]. unfold in_range.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=56763570144.761931854156.7000004008S2HaS2Hn".
rewrite wa_unsigned by lia. rewrite unsigned_lit by lia. rewrite orb_false_r. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section MemEffects.
Variable segs : list Segment.
#[using="Type"] Lemma rw_cells_CB_prefix_write : forall m A n junk bs,
rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
rw_cells segs (write_to_mem m (wa A) bs) A [CB (length bs) bs; CB (n - length bs) (skipn (length bs) junk)].
Proof.
intros m A n junk bs [[Hwf Hb] Hw] Hlen. cbn in Hwf. destruct Hwf as [Hj _].
cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
split; [split|].
- cbn. repeat split; try reflexivity. rewrite skipn_length. Local Ltac2 Set LiaHints.tbl := fun () => "0040>15032544732.1025829515929.1059853491348.1066103515825.1000000900B00K00TS2Hj4HlenS2Hj4HlenS2Hj4HlenS2Hj4Hlen".
lia.
- cbn [cells_bytes cbytes]. rewrite app_nil_r.
pose proof (bytes_at_write_inside segs m A junk 0 bs Hb ltac:(lia) ltac:(cbn; lia)) as W.
rewrite Z.add_0_r in W. unfold upd_bytes in W. cbn [firstn app Nat.add] in W. exact W.
- cbn [cells_size csize]. cbn [cells_size csize] in Hw. replace (length bs + (n - length bs + 0))%nat with (n + 0)%nat by lia.
apply wr_at_write. exact Hw.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_CB_store_ok : forall m A n junk k,
rw_cells segs m A [CB n junk] -> (k <= n)%nat -> store_ok segs m (wa A) k = true.
Proof.
intros m A n junk k [_ Hw] Hk. cbn [cells_size csize] in Hw.
rewrite <- (Z.add_0_r A). apply (wr_at_store_ok segs m A (Z.of_nat (n + 0))); [exact Hw|lia|lia].
Qed.
#[using="Type"] Lemma mem_inv_syswrite : forall m A n junk bs,
mem_inv segs m -> rw_cells segs m A [CB n junk] -> (length bs <= n)%nat ->
mem_inv segs (write_to_mem m (wa A) bs).
Proof.
intros. apply mem_inv_store; [assumption|]. eapply rw_cells_CB_store_ok; eauto.
Qed.
Section Zeros.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_zeros m [(wa a, Z_to_bv 64 n)].
#[using="Ha Hn Han"] Lemma zeros_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. Local Ltac2 Set LiaHints.tbl := fun () => "0010>45074079485.1200000?S2Ha2Hn2Hx1l2l0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma zeros_inside : forall x, (a <= bv_unsigned x < a + n)%Z -> m' x = Some (Z_to_bv 8 0).
Proof.
intros x Hx. unfold m'. rewrite apply_zeros_spec by assumption. unfold in_range.
Local Ltac2 Set LiaHints.tbl := fun () => "0030>57195748153.1257197819110.1257197819237.1200000=00D00QS2Ha2Hn2Hx2n0S2Hx2n0S2Ha2Hn2Hx2n0".
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma wview_zeros_mono : forall x, wview segs m x <> None -> wview segs m' x <> None.
Proof.
intros x Hx. unfold wview in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n x); [discriminate| exact Hx].
Qed.
#[using="Ha Hn Han"] Lemma bytes_at_zeros_other : forall A bs,
bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
intros A bs (H0 & H1 & H) Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1312061531.14 24931804653.1437801082799.168548742317.16 00000400800B00OS2H1S2H0S2H02H12HiS2Ha2Hn2Hd2Hi".
split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma wr_at_zeros : forall A k, wr_at segs m A k -> wr_at segs m' A k.
Proof. intros A k (H0 & H1 & H). Local Ltac2 Set LiaHints.tbl := fun () => "0020>24938099585.1351444846388.13000004008S2H0S2H1".
split; [lia|]. split; [lia|]. intros i Hi. apply wview_zeros_mono, H, Hi. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma rw_cells_zeros_other : forall A cs,
rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_zeros. exact Hw.
Qed.
#[using="Ha Hn Han"] Lemma ro_cells_zeros_other : forall A cs,
ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_zeros_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
#[using="Ha Hn Han"] Lemma stk_zeros : forall lo hi, stk segs m lo hi -> stk segs m' lo hi.
Proof.
intros lo hi (H0 & H1 & H). Local Ltac2 Set LiaHints.tbl := fun () => "0020>29432667347.1352365100048.13000004008S2H0S2H1".
split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)]. split; [apply wview_zeros_mono; exact Hw|].
unfold mrd in *. unfold m'. rewrite apply_zeros_spec by assumption.
destruct (in_range a n (wa x)); [eexists; reflexivity|]. exists b. exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma munch_zeros : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite zeros_outside. { apply H. exact Hx. }
Local Ltac2 Set LiaHints.tbl := fun () => "0030>30923322781.179193465178.16 9193465178.17 00000700:00=S2n02n1S1lS1l".
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma wmono_zeros : forall m0, wmono segs m0 m -> wmono segs m0 m'.
Proof. intros m0 H x Hx. apply wview_zeros_mono, H, Hx. Qed.
#[using="Ha Hn Han"] Lemma mem_inv_zeros : mem_inv segs m -> (forall x : word, (a <= bv_unsigned x < a + n)%Z -> ro_addr segs x = false) -> mem_inv segs m'.
Proof.
intros Hinv Hro x b Hx. unfold m' in Hx. rewrite apply_zeros_spec in Hx by assumption.
unfold in_range in Hx.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb] in Hx;
try exact (Hinv _ _ Hx).
apply Hro. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30923355166.15000006S1l2l0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma bytes_at_zeros_new : bytes_at segs m' a (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=1607731481.1018483514614.826983018816.87985991279.1000000400<00@00KS2HiS2Ha3HanS2HaS2Ha3Han2Hi".
split; [lia|]. rewrite repeat_length. split; [lia|]. intros i Hi.
unfold mrd. rewrite zeros_inside. 2:{ rewrite wa_unsigned by lia. lia. }
symmetry. apply nth_error_repeat. exact Hi.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma wr_at_zeros_new : wr_at segs m' a n.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>26983018816.8 34386660111.1045608532938.8 6882689537.10 00000400800=00HS2HaS2HiS3HanS2Ha3Han2Hi".
split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite zeros_inside; [discriminate|].
rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma rw_cells_zeros_new : rw_cells segs m' a [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))].
Proof.
split; [split|].
- cbn. split; [apply repeat_length| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_zeros_new.
- cbn [cells_size csize]. Local Ltac2 Set LiaHints.tbl := fun () => "0010<2424346617.8000004S2Hn".
rewrite Nat.add_0_r, Z2Nat.id by lia. apply wr_at_zeros_new.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Zeros.
Section Unmaps.
Variables (m : word -> option byte) (a n : Z).
Hypothesis Ha : (0 <= a < 2^64)%Z.
Hypothesis Hn : (0 <= n < 2^64)%Z.
Hypothesis Han : (a + n <= 2^64)%Z.
Let m' := apply_unmaps m [(wa a, Z_to_bv 64 n)].
#[using="Ha Hn Han"] Lemma unmaps_outside : forall x, (bv_unsigned x < a \/ a + n <= bv_unsigned x)%Z -> m' x = m x.
Proof.
intros x Hx. unfold m'. rewrite apply_unmaps_spec by assumption. unfold in_range.
destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + n)); cbn [andb]; try reflexivity. Local Ltac2 Set LiaHints.tbl := fun () => "0010>17133481006.1200000?S2Ha2Hn2Hx1l2l0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma bytes_at_unmaps_other : forall A bs,
bytes_at segs m A bs -> (A + Z.of_nat (length bs) <= a \/ a + n <= A)%Z -> bytes_at segs m' A bs.
Proof.
intros A bs (H0 & H1 & H) Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0040>1312061531.14 24931804653.1437801082799.168548742317.16 00000400800B00OS2H1S2H0S2H02H12HiS2Ha2Hn2Hd2Hi".
split; [lia|]. split; [lia|]. intros i Hi.
unfold mrd. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma wr_at_unmaps_other : forall A k,
wr_at segs m A k -> (A + k <= a \/ a + n <= A)%Z -> wr_at segs m' A k.
Proof.
intros A k (H0 & H1 & H) Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0040>20565884745.1624931804653.1433628179521.1651442751832.1400000=00A00K00OS2Ha2Hn2Hd2HiS2H0S2H02H12HiS2H1".
split; [lia|]. split; [lia|]. intros i Hi.
unfold wview. rewrite unmaps_outside. { apply H. exact Hi. } rewrite wa_unsigned by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma rw_cells_unmaps_other : forall A cs,
rw_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> rw_cells segs m' A cs.
Proof.
intros A cs [[Hwf Hb] Hw] Hd. split; [split; [exact Hwf|]|].
- apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
- apply wr_at_unmaps_other; [exact Hw| exact Hd].
Qed.
#[using="Ha Hn Han"] Lemma ro_cells_unmaps_other : forall A cs,
ro_cells segs m A cs -> (A + Z.of_nat (cells_size cs) <= a \/ a + n <= A)%Z -> ro_cells segs m' A cs.
Proof.
intros A cs [Hwf Hb] Hd. split; [exact Hwf|].
apply bytes_at_unmaps_other; [exact Hb|]. rewrite cells_bytes_length by assumption. exact Hd.
Qed.
#[using="Ha Hn Han"] Lemma stk_unmaps_other : forall lo hi, stk segs m lo hi -> (hi <= a \/ a + n <= lo)%Z -> stk segs m' lo hi.
Proof.
intros lo hi (H0 & H1 & H) Hd. Local Ltac2 Set LiaHints.tbl := fun () => "0040>29430565567.1437158057020.1952367200892.145744836320.19 00000400;00?00IS2H0S2Hd2HxS2H1S2H02H12Hx".
split; [lia|]. split; [lia|]. intros x Hx.
destruct (H x Hx) as [Hw (b & Hb)].
assert (E : m' (wa x) = m (wa x)). { apply unmaps_outside. rewrite wa_unsigned by lia. lia. }
split. { unfold wview in *. rewrite E. exact Hw. } exists b. unfold mrd in *. rewrite E. exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma munch_unmaps : forall W m0, munch W m0 m -> inside W a n -> munch W m0 m'.
Proof.
intros W m0 H Hin x Hx. pose proof (bv_unsigned_in_range 64 x).
rewrite unmaps_outside. { apply H. exact Hx. }
Local Ltac2 Set LiaHints.tbl := fun () => "0030>30923322781.179193465178.16 9193465178.17 00000700:00=S2n02n1S1lS1l".
destruct (Z.ltb_spec0 (bv_unsigned x) a); [lia|].
destruct (Z.leb_spec0 (a + n) (bv_unsigned x)); [lia|].
exfalso. eapply (inside_not_outside W a n (bv_unsigned x) Hin); [lia| exact Hx].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Ha Hn Han"] Lemma mem_inv_unmaps : mem_inv segs m -> mem_inv segs m'.
Proof.
intros Hinv x b Hx. unfold m' in Hx. rewrite apply_unmaps_spec in Hx by assumption.
destruct (in_range a n x); [discriminate|]. exact (Hinv _ _ Hx).
Qed.
End Unmaps.
End MemEffects.
Lemma rw_cells_wr_at : forall segs m A cs n,
rw_cells segs m A cs -> (n <= Z.of_nat (cells_size cs))%Z -> wr_at segs m A n.
Proof. intros segs m A cs n [_ (H0 & H1 & H)] Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0030>19524649394.1123369229869.9 24931803367.9 00000700>00BS2Hn2HiS2H12HnS2H0".
split; [lia|]. split; [lia|]. intros i Hi. apply H. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma rw_cells_bytes_at : forall segs m A cs, rw_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [[_ H] _]. exact H. Qed.
Lemma ro_cells_bytes_at : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.
Ltac at_node_solve :=
at_node_red; split_spine;
first [ reflexivity | lia | assumption
| symmetry; apply Z_to_bv_bv_unsigned
| lazymatch goal with
| |- wr_at ?segs ?m ?A ?n =>
match goal with H : rw_cells segs m A ?cs |- _ =>
apply (rw_cells_wr_at segs m A cs n H); cbn [cells_size csize]; lia end
| |- bytes_at ?segs ?m ?A ?bs =>
match goal with
| H : rw_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (rw_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
| H : ro_cells segs m A ?cs |- _ =>
apply (bytes_at_ext segs m A _ bs (ro_cells_bytes_at segs m A cs H));
cbn [cells_bytes cbytes]; rewrite ?app_nil_r; reflexivity
end
end
| idtac ].
Ltac sys_mem_write :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?ro) =>
change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
lazymatch goal with
| H : rw_cells segs m B [CB ?n ?junk] |- _ =>
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
(try lazymatch goal with
| HI : mem_inv segs m |- _ =>
let HI' := fresh "MI" in
pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
end);
let H' := fresh "DST" in
pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
clear H;
transport_chunks segs m B bs;
footprint_after_store segs m B bs;
let m' := fresh "m" in
remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; rename H' into H
| _ => fail "sys_mem_write: no hypothesis rw_cells" segs m B "[CB _ _]"
end
end.
Lemma apply_mem_zeros : forall m z, apply_writes (apply_zeros (apply_unmaps m []) [z]) [] = apply_zeros m [z].
Proof. reflexivity. Qed.
Lemma apply_mem_unmaps : forall m u, apply_writes (apply_zeros (apply_unmaps m [u]) []) [] = apply_unmaps m [u].
Proof. reflexivity. Qed.
Ltac transport_zeros segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_zeros_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_zeros segs m a n Ha Hn Han A2 n2) in H
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_zeros_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (not provably disjoint from zero-fill):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ => apply (stk_zeros segs m a n Ha Hn Han lo hi) in H
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_zeros m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
| fail 100 "zero-filled range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => apply (wmono_zeros segs m a n Ha Hn Han m0) in H
| H : mem_inv segs m |- _ =>
let H' := fresh "MI" in
assert (H' : mem_inv segs (apply_zeros m [(wa a, Z_to_bv 64 n)]))
by (apply (mem_inv_zeros segs m a n Ha Hn Han H); first [assumption | intros; shelve]);
clear H
end.
Ltac sys_mem_zeros :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_zeros ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_zeros m [(A, Z_to_bv 64 n)]) with (apply_zeros m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hza" in let Hn := fresh "Hzn" in let Han := fresh "Hzan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_zeros segs m a n Ha Hn Han;
let Z' := fresh "ZNEW" in
pose proof (rw_cells_zeros_new segs m a n Ha Hn Han) as Z';
let m' := fresh "m" in
remember (apply_zeros m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.
Ltac transport_unmaps segs m a n Ha Hn Han :=
repeat match goal with
| H : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ apply (bytes_at_unmaps_other segs m a n Ha Hn Han A2 bs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : wr_at segs m ?A2 ?n2 |- _ =>
first [ apply (wr_at_unmaps_other segs m a n Ha Hn Han A2 n2) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (rw_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ apply (ro_cells_unmaps_other segs m a n Ha Hn Han A2 cs2) in H; [|simpl_sizes; slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : stk segs m ?lo ?hi |- _ =>
first [ apply (stk_unmaps_other segs m a n Ha Hn Han lo hi) in H; [|slia]
| idtac "note: dropping hypothesis (inside unmapped range):" H; clear H ]
| H : munch ?W ?m0 m |- _ =>
first [ apply (munch_unmaps m a n Ha Hn Han W m0) in H; [|cbn [inside]; slia]
| fail 100 "unmapped range not inside the declared footprint" ]
| H : wmono segs ?m0 m |- _ => idtac "note: dropping wmono (not preserved by an unmap):" H; clear H
| H : mem_inv segs m |- _ => apply (mem_inv_unmaps segs m a n Ha Hn Han) in H
end.
Ltac sys_mem_unmaps :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
assert (Ha : (0 <= a < 2^64)%Z) by lia;
assert (Hn : (0 <= n < 2^64)%Z) by lia;
assert (Han : (a + n <= 2^64)%Z) by lia;
transport_unmaps segs m a n Ha Hn Han;
let m' := fresh "m" in
remember (apply_unmaps m [(wa a, Z_to_bv 64 n)]) as m' eqn:Heqm;
clear Heqm Ha Hn Han; try clear m
end.
Ltac sys_nret :=
cbv beta delta [efferr_ci eff0_ci efferr eff0];
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_none
| rewrite apply_mem_delivered; sys_mem_write
| rewrite apply_mem_write; sys_mem_write
| rewrite apply_mem_zeros; sys_mem_zeros
| rewrite apply_mem_unmaps; sys_mem_unmaps
| idtac ].
Ltac sys_nret_raw :=
cbv beta delta [efferr_ci eff0_ci efferr eff0];
rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs;
(lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4) _ _ _ _) =>
let p' := eval vm_compute in (p + 4)%Z in
replace (Z_to_bv 64 p + Z_to_bv 64 4 : word) with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
| _ => idtac
end);
first [ rewrite apply_mem_zeros | rewrite apply_mem_unmaps ].
Notation errno_addr tp := (bv_unsigned tp + (-164))%Z (only parsing).
Definition sysret_val (r : word) : word :=
match errno_of r with Some _ => Z_to_bv 64 (-1) | None => r end.
Definition sysret_errno (r errv : word) : word :=
match errno_of r with Some e => Z_to_bv 64 e | None => errv end.
Lemma errno_of_big : forall r, (2^64 - 4096 < bv_unsigned r)%Z -> errno_of r = Some (2^64 - bv_unsigned r)%Z.
Proof. intros r H. unfold errno_of. Local Ltac2 Set LiaHints.tbl := fun () => "0010=65851334225.3000005S1H1n".
destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [reflexivity|lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma negw_errno : forall u, (2^64 - 4096 < u < 2^64)%Z -> bv_swrap 32 (0 - u) = (2^64 - u)%Z.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=16039838181.21679810303.2 38715784328.243010535844.2000004005006007S2HuSSS".
replace (0 - u + 2^31)%Z with ((2^64 - u + 2^31) + (- 2^32) * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma swrap32_small : forall z, (-2^31 <= z < 2^31)%Z -> bv_swrap 32 z = z.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=46065261573.250762911644.2000001005SS2Hz".
rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma swrap32_high : forall u, (2^64 - 2^31 <= u < 2^64)%Z -> bv_swrap 32 u = (u - 2^64)%Z.
Proof.
intros u Hu. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 32)%Z with (2^32)%Z. change (2 ^ 32 `div` 2)%Z with (2^31)%Z.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=16039838181.238715784328.242229362553.256826369127.2000004005006007S2HuSSS".
replace (u + 2^31)%Z with ((u - 2^64 + 2^31) + 2^32 * 2^32)%Z by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma unsigned_errno_ret : forall e, (1 <= e <= 4095)%Z -> bv_unsigned (errno_ret e) = (2^64 - e)%Z.
Proof. intros. rewrite errno_ret_unsigned by lia. reflexivity. Qed.
Lemma Z_to_bv_minus_mod : forall z, Z_to_bv 64 (z - 2^64) = Z_to_bv 64 z.
Proof.
intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with (2^64)%Z.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=11608664069.126654508554.1000001002SS".
replace (z - 2^64)%Z with (z + (-1) * 2^64)%Z by lia. apply Z.mod_add. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sextw_errno : forall e, (1 <= e <= 2^31)%Z ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (errno_ret e) + 0)) = errno_ret e.
Proof.
intros e He. unfold errno_ret. rewrite unsigned_lit_wrap.
replace ((- e) mod 2^64)%Z with (2^64 - e)%Z.
2:{ Local Ltac2 Set LiaHints.tbl := fun () => "0050=11601618584.241619017780.249047432196.250358273775.261118559584.200000100200300700;SSSS2HeS2He".
replace (-e)%Z with ((2^64 - e) + (-1) * 2^64)%Z by lia. rewrite Z.mod_add; [|lia]. rewrite Z.mod_small; [reflexivity|lia]. }
rewrite Z.add_0_r, swrap32_high by lia. f_equal. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma sextw_small : forall z, (0 <= z < 2^31)%Z ->
Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0)) = Z_to_bv 64 z.
Proof. intros z Hz. Local Ltac2 Set LiaHints.tbl := fun () => "0020=25080995374.238557618280.2000004008S2HzS2Hz".
rewrite unsigned_lit by lia. rewrite Z.add_0_r, swrap32_small by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stk_lo_nonneg : forall segs m lo hi, stk segs m lo hi -> (0 <= lo)%Z.
Proof. intros segs m lo hi (H & _). exact H. Qed.
Ltac name_sp sp k :=
let sp1 := fresh "sp" in let E := fresh "Esp" in let H := fresh "Hsp" in
remember (Z_to_bv 64 (bv_unsigned sp + k)) as sp1 eqn:E;
assert (H : bv_unsigned sp1 = (bv_unsigned sp + k)%Z)
by (rewrite E; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *;
try match goal with ST : stk _ _ _ _ |- _ => pose proof (stk_lo_nonneg _ _ _ _ ST) end;
apply unsigned_lit; lia).
Ltac unname_sp :=
match goal with
| H : bv_unsigned ?sp1 = (bv_unsigned ?sp + ?k)%Z, E : ?sp1' = Z_to_bv 64 (bv_unsigned ?sp + ?k) |- _ =>
constr_eq sp1 sp1';
repeat match goal with K : context [bv_unsigned sp1] |- _ => tryif constr_eq K H then fail else rewrite H in K end;
try rewrite H; clear H; subst sp1
end.
Tactic Notation "call_sp" uconstr(SPEC) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
name_sp sp k; call SPEC; unname_sp
| _ => call SPEC
end.
Ltac sys_finish :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
hnf;
repeat (lazymatch goal with |- ex _ => eexists end);
lazymatch goal with
| |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
| |- _ = _ => cbv delta [mkR]; reflexivity
end;
repeat match goal with |- _ /\ _ => split end; try assumption.
Lemma impl_from_evt : forall {node : Type} segs (atn : node -> machine_state -> Prop) {R} (t : itree node R) Q ms,
evt segs (fun ms' => impl segs atn t Q ms') ms -> impl segs atn t Q ms.
Proof. intros node segs atn R t Q ms H. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.
Ltac iprefix := apply impl_from_evt.
Tactic Notation "icall" uconstr(SPEC) :=
(lazymatch goal with |- evt _ _ _ => apply evt_done | _ => idtac end);
first [ eapply SPEC
| eapply impl_epost_mono; [ eapply SPEC | ] ].
Ltac ipost segs :=
let a := fresh "ans" in let ms' := fresh "ms'" in let PO := fresh "POST" in
intros a ms' PO;
destruct_exs PO;
let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
destruct PO as [E [MUc [WMc PO]]];
first [ destruct PO as [MIc PO] | rename PO into MIc ];
subst ms';
lazymatch type of MUc with
| munch _ ?m ?m' =>
transport_after_call segs m m' MUc WMc;
clear MUc WMc;
try match goal with H : mem_inv segs m |- _ => clear H end;
try clear m
end;
try destruct_ands PO;
try (let MIname := fresh "MI" in
lazymatch goal with H : mem_inv segs _ |- _ => rename H into MIname; try rename MIname into MI end);
repeat match goal with
| |- context [ret_pc (Z_to_bv 64 ?n)] => is_Zlit n;
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
end.
