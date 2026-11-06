(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX Bytes InitMem Mem Cells Frame.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABytes StdioFiles Stdio_kit Stdio_iface F_syscalls AF_atexit AExit F_module_dtor ADriver_iface.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require AsanHexScan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require ARepInit_kit ARepInit_B.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
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
Section CANSEC1. Context {rc : runConstT}.
Definition ho_pfact_eqb (f g : pfact) : bool :=
match f, g with
| PVar n lo hi, PVar n' lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
| PRange e lo hi, PRange e' lo' hi' => zexp_eqb e e' && Z.eqb lo lo' && Z.eqb hi hi'
| PDisj a1 n1 a2 n2, PDisj a1' n1' a2' n2' => zexp_eqb a1 a1' && Z.eqb n1 n1' && zexp_eqb a2 a2' && Z.eqb n2 n2'
| _, _ => false
end.
#[using="Type"] Lemma ho_pfact_eqb_eq : forall f g, ho_pfact_eqb f g = true -> f = g.
Proof.
intros f g H. destruct f, g; cbn in H; try discriminate;
repeat (apply andb_prop in H as [H ?X]);
repeat match goal with
| K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
| K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K
| K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
end; subst; reflexivity.
Qed.
#[using="Type"] Lemma ho_pfact_find : forall V (l : list pfact) f,
Forall (pfact_ok V) l -> existsb (ho_pfact_eqb f) l = true -> pfact_ok V f.
Proof.
intros V l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply ho_pfact_eqb_eq in Hg. subst g.
exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.
End CANSEC1.
Ltac mf V m HM f H := pose proof (mfact_find asegs V m _ f HM ltac:(vm_compute; reflexivity)) as H; cbn [mfact_ok zv cellw] in H.
Ltac pf V HP f H := pose proof (ho_pfact_find V _ f HP ltac:(vm_compute; reflexivity)) as H; cbn [pfact_ok zv] in H.
Section CANSEC2. Context {rc : runConstT}.
#[using="Type"] Lemma aimg_chunk : forall V m (l : list mfact) A cs,
Forall (mfact_ok asegs V m) l ->
existsb (fun f => match f with MImg lo' hi' => (lo' <=? A) && (A + Z.of_nat (cells_size cs) <=? hi') | _ => false end) l = true ->
cells_wf cs -> rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 ->
rw_cells asegs m A cs.
Proof.
intros V m l A cs HM HE WF HB HA HHI.
pose proof (cells_bytes_length cs WF) as LEN.
assert (R : forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None).
{ eapply mimg_cover; [exact HM| exact HE]. }
eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
- intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>18516291689.16000008S3LEN2Ha".
lia.
- exact HB.
- exact HA.
- rewrite LEN. exact HHI.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
Ltac aimg V m HM A cs H :=
pose proof (aimg_chunk V m _ A cs HM ltac:(vm_compute; reflexivity) ltac:(cbn; repeat split; exact I)
ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as H.
Notation z64 := (Z_to_bv 64 0).
Section CANSEC3. Context {rc : runConstT}.
#[using="Type"] Lemma stderr_wfile0_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> stderr_wfile0 m.
Proof.
intros V m HM. exists (Z_to_bv 64 5), z64, 0, 0, (repeat (Z_to_bv 8 0) 80).
Local Ltac2 Set LiaHints.tbl := fun () => "0030=16376473098.450085102877.48276998545.4 000001002003SSS".
split; [| split; [vm_compute; reflexivity| split; [left; reflexivity| lia]]].
aimg V m HM 0x9dd38 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x5f5b18 0 2 z64 0xffffffff (repeat (Z_to_bv 8 0) 80)) H. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stdout_file_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> stdout_file m stdout_init.
Proof.
intros V m HM. exists (Z_to_bv 64 5), z64, (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
cbn [so_active so_buf so_lbf_nl so_first stdout_init Prelim.zlength length Z.of_nat Z.add].
split. { Local Ltac2 Set LiaHints.tbl := fun () => "0050=21928638730.429264482449.443365953299.444684045841.44561878410.4 000001002003004005SSSSS".
aimg V m HM 0x9de28 (file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE 0x5f5b20 1024 1 z64 10 (repeat (Z_to_bv 8 0) 80)) H. exact H. }
split; [vm_compute; reflexivity|].
split. { aimg V m HM 0x5f5b20 [CB 1024 (repeat (Z_to_bv 8 0) 1024)] H. exact H. }
split; [reflexivity|]. split; [unfold zlength; cbn; lia| intros _; reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma canary_seg_bytes : forall k, (k < 8)%nat ->
segment_byte_at (seg_bytes Asan_segment_003) (0x5f5450 - 0x9b000 + N.of_nat k)%N = Some (Z_to_bv 8 0).
Proof. intros k Hk. do 8 (destruct k as [|k]; [vm_compute; reflexivity|]). Local Ltac2 Set LiaHints.tbl := fun () => "0010=41133976870.3000004S2Hk".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma canary_wr_at : forall m, wr_at asegs m 0x5f5450 8.
Proof.
intros m. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>10481949851.5 12823396645.5 14833545585.2 2130131615.13 24697392276.7 24697392276.9 24697392407.1124697392407.9 24697392534.1124697425044.7 24697425044.9 24697425175.1124697425175.9 24697425302.1124697425425.1324703689674.7 24703722184.7 33296397231.2 43077602292.1343077634163.1343077635060.139813156684.13 00000400800900=00C00D00E00L00S00Z00a00h00o01601701801>01?01F01M01T01XS2HiS2HiSS2HiS2Hi1nFFS2Hi2n0S2Hi2n1S2Hi2l0S2Hi2l0S2Hi2l1S2Hi2l1S2Hi2l2FFS2Hi1lSS2Hi2n2S2Hi2n2S2Hi2n2S2Hi".
split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
destruct (m (wa (0x5f5450 + i))) as [b|] eqn:E; [discriminate|].
rewrite wa_unsigned by lia. rewrite a_find_segment_1 by lia.
destruct (Z.leb_spec0 0x10000 (0x5f5450 + i)); destruct (Z.leb_spec0 (0x5f5450 + i + 1) 0x31000); cbn [andb]; try lia.
destruct (Z.leb_spec0 0x31000 (0x5f5450 + i)); destruct (Z.leb_spec0 (0x5f5450 + i + 1) 0x99000); cbn [andb]; try lia.
destruct (Z.leb_spec0 0x99000 (0x5f5450 + i)); destruct (Z.leb_spec0 (0x5f5450 + i + 1) 0x9b000); cbn [andb]; try lia.
destruct (Z.leb_spec0 0x9b000 (0x5f5450 + i)); destruct (Z.leb_spec0 (0x5f5450 + i + 1) 0x5f7000); cbn [andb]; try lia.
replace (seg_writable Asan_segment_003) with true by (vm_compute; reflexivity).
replace (Z.of_N (seg_base Asan_segment_003)) with 0x9b000 by (vm_compute; reflexivity).
replace (Z.to_N (0x5f5450 + i - 0x9b000)) with (0x5f5450 - 0x9b000 + N.of_nat (Z.to_nat i))%N by lia.
rewrite canary_seg_bytes by lia. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ssp_guard_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m ssp_guard [C8 (Z_to_bv 64 (V 45%nat))].
Proof.
intros V m HM. mf V m HM (MRo (ZLit 6247504) 8 (ZV 45)) H. unfold ssp_guard.
pose proof (cellw_bytes 8 (V 45%nat) eq_refl) as (Cb & Cs & Cwf). change (cellw 8 (V 45%nat)) with (C8 (Z_to_bv 64 (V 45%nat))) in Cb, Cs, Cwf.
split.
- split; [cbn; split; [exact Cwf| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r, Cb. exact H.
- cbn [cells_size]. rewrite Cs. apply canary_wr_at.
Qed.
#[using="Type"] Lemma errno_init : forall V m, Forall (mfact_ok asegs V m) asan_mem_facts -> rw_cells asegs m 0x5d536c [C4 z64].
Proof. intros V m HM. aimg V m HM 0x5d536c [C4 z64] H. exact H. Qed.
#[using="Type"] Lemma run_rw_cells : forall m A n (b : byte),
0 <= n -> (forall i, 0 <= i < n -> m (wa (A + i)) = Some b) -> wr_at asegs m A n ->
rw_cells asegs m A [CB (Z.to_nat n) (repeat b (Z.to_nat n))].
Proof.
intros m A n b Hn Hz (W1 & W2 & W3). split.
- split; [cbn; split; [rewrite repeat_length; reflexivity| exact I]|].
cbn [cells_bytes cbytes]. rewrite app_nil_r. Local Ltac2 Set LiaHints.tbl := fun () => "0040>23369468918.102425231845.10 24931650876.10548305750.12  00000400800<00@S2W2S2HnS2W1S2Hi".
split; [lia|]. split; [rewrite repeat_length, Z2Nat.id by lia; lia|].
intros i Hi. rewrite repeat_length in Hi. rewrite (nth_error_repeat b Hi).
unfold mrd. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. exact W3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bytes_eq_of_unsigned : forall (bs bs' : list byte), map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof.
induction bs as [|b bs IH]; intros [|b' bs'] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hb Hbs. f_equal; [apply bv_eq; exact Hb| apply IH; exact Hbs].
Qed.
#[using="Type"] Lemma rw_C8_C4 : forall m A (v lo hi : word),
rw_cells asegs m A [C8 v] -> cells_bytes [C4 lo; C4 hi] = cells_bytes [C8 v] -> rw_cells asegs m A [C4 lo].
Proof.
intros m A v lo hi H E.
assert (H' : rw_cells asegs m A ([C4 lo] ++ [C4 hi])).
{ eapply rw_cells_recast; [exact H| cbn; tauto| exact E| reflexivity]. }
apply (proj1 (rw_cells_app asegs m A _ _)) in H'. exact (proj1 H').
Qed.
#[using="Type"] Lemma wr_at_sub' : forall m a n a' n', wr_at asegs m a n -> 0 <= a' -> a <= a' -> a' + n' <= a + n -> wr_at asegs m a' n'.
Proof.
intros m a n a' n' (W1 & W2 & W3) H0 H1 H2. Local Ltac2 Set LiaHints.tbl := fun () => "0040>2110276096.14 22615015996.144856259436.12 48935769329.1200000100;00B00FSS2H12H22HiS2W22H2S2H0".
split; [lia|]. split; [lia|]. intros i Hi.
replace (a' + i) with (a + (a' - a + i)) by lia. apply W3. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC3.
Section CANSEC4. Context {rc : runConstT}.
#[using="Type"] Lemma zchunk_pointwise : forall m A n, rw_cells asegs m A [CB (Z.to_nat n) (zeros n)] -> 0x5f7000 <= A ->
forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0).
Proof.
intros m A n [[_ B] _] HA i Hi. cbn [cells_bytes cbytes app] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
unfold zeros in B1, B. rewrite repeat_length in B1, B.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>10351595562.1033628179521.1052674177036.1061943176380.1000000700A00H00RS2B12HiS2B12HA2HiS2B12HiS2B12HA2Hi".
specialize (B (Z.to_nat i) ltac:(lia)).
rewrite (nth_error_repeat (Z_to_bv 8 0)) in B by lia. rewrite Z2Nat.id in B by lia.
rewrite ref_mrd_overlay in B; [exact B|]. right. rewrite wa_unsigned; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition zlit_of (e : zexp) : option Z := match e with ZLit z => Some z | _ => None end.
#[using="Type"] Lemma zlit_of_zv : forall V e z, zlit_of e = Some z -> zv V e = z.
Proof. intros V e z H. destruct e; cbn in H; try discriminate. injection H as ->. reflexivity. Qed.
Definition mzero_covb (lo n : Z) (f : mfact) : bool :=
match f with
| MZero a n' => match zlit_of a with Some a' => (a' <=? lo) && (lo + n <=? a' + n') | None => false end
| MZeroC a n' => match zlit_of a with Some a' => (0x5f7000 <=? a') && ((a' <=? lo) && (lo + n <=? a' + n')) | None => false end
| _ => false
end.
#[using="Type"] Lemma mzero_cover : forall V m (l : list mfact) lo n,
Forall (mfact_ok asegs V m) l -> existsb (mzero_covb lo n) l = true ->
forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0).
Proof.
intros V m l lo n HM HE i Hi. apply existsb_exists in HE as (f & Hin & Hf).
pose proof (proj1 (Forall_forall _ _) HM f Hin) as K.
destruct f as [? ? ?|a k|? ? ?|a k|? ? ?|? ?|? ?|? ?|? ?]; try discriminate; cbn [mzero_covb] in Hf;
destruct (zlit_of a) as [a'|] eqn:E; try discriminate; apply (zlit_of_zv V) in E; cbn [mfact_ok] in K; rewrite E in K.
- apply andb_prop in Hf as [H0 Hf]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>21312125675.1721312125675.185003675858.18 65010095206.1765010095206.1800000:00D00H00I00JS2H12H22HiS2H12H22HiS2H0SS".
replace (lo + i) with (a' + (lo + i - a')) by lia. apply (zchunk_pointwise m a' k K); lia.
- apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
replace (lo + i) with (a' + (lo + i - a')) by lia. apply K. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition mknownb (l : list mfact) (a : Z) : bool :=
existsb (fun f => match f with
| MZero (ZLit a0) n => (a0 <=? a) && (a <? a0 + n)
| MZeroC (ZLit a0) n => (a0 <=? a) && (a <? a0 + n)
| MFill (ZLit a0) n _ => (a0 <=? a) && (a <? a0 + n)
| MCell (ZLit a0) w _ => (a0 <=? a) && (a <? a0 + Z.of_nat w) && (Nat.eqb w 1 || Nat.eqb w 2 || Nat.eqb w 4 || Nat.eqb w 8)
| _ => false
end) l.
#[using="Type"] Lemma cellw_bytes_len : forall w z, (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%nat -> length (cbytes (cellw w z)) = w /\ csize (cellw w z) = w.
Proof. intros w z [ -> | [ -> | [ -> | -> ] ] ]; cbn; split; reflexivity. Qed.
#[using="Type"] Lemma mrd_high0 : forall m a, 0x5f7000 <= a < 2^64 -> mrd asegs m (wa a) = m (wa a).
Proof. intros m a Ha. apply ref_mrd_overlay. Local Ltac2 Set LiaHints.tbl := fun () => "0020=56765667309.460849098329.4000004008S2HaS2Ha".
rewrite wa_unsigned by lia. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mknown_some : forall V m l a, Forall (mfact_ok asegs V m) l -> 0x5f7000 <= a < 2^64 -> mknownb l a = true ->
exists b, m (wa a) = Some b.
Proof.
intros V m l a HF HA HK. apply existsb_exists in HK as (f & Hin & Hf). pose proof (proj1 (Forall_forall _ _) HF f Hin) as OK.
destruct f as [e w v|e n|e w v|e n|e n c|lo hi|e n|e n|e n]; try discriminate; destruct e; try discriminate; cbn [mfact_ok zv] in OK.
- apply andb_prop in Hf as [Hf HW]. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
assert (W : (w = 1 \/ w = 2 \/ w = 4 \/ w = 8)%nat).
{ Local Ltac2 Set LiaHints.tbl := fun () => "00?0>28989570692.153484486402.14 3486681858.17 47572180885.1750217586392.1350217586392.1457858575114.1857860442890.155940200012.14 5946672579.13 5946672579.14 5946720844.17 6353031576.14 6354899352.17 8822925381.14 00000400;00B00L00S00Z00f01201601701801<01C01J01TS2HWS2H12WFS2H12LBS2H12H22LBS2H12H2S2H12H2S2H12H21E2LBS2H12H22WF1ES2WFSSS2LBS2HA2WFS2HA2LBS2H12H22WF".
repeat (apply orb_prop in HW as [HW|HW]); apply Nat.eqb_eq in HW; lia. }
destruct (cellw_bytes_len w (zv V v) W) as [LB _].
destruct OK as [[_ [_ [_ B]]] _]. cbn [cells_bytes] in B. rewrite app_nil_r in B.
specialize (B (Z.to_nat (a - z)) ltac:(rewrite LB; lia)). rewrite Z2Nat.id in B by lia. replace (z + (a - z)) with a in B by lia.
rewrite (mrd_high0 m a) in B by lia.
destruct (nth_error (cbytes (cellw w (zv V v))) (Z.to_nat (a - z))) as [b|] eqn:E; [exists b; exact B|].
apply nth_error_None in E. rewrite LB in E. lia.
- apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
destruct OK as [[[WF _] [_ [_ B]]] _]. cbn [cells_bytes cbytes cells_wf cell_wf] in B, WF. rewrite app_nil_r in B.
specialize (B (Z.to_nat (a - z)) ltac:(lia)). rewrite Z2Nat.id in B by lia. replace (z + (a - z)) with a in B by lia.
rewrite (mrd_high0 m a) in B by lia.
destruct (nth_error (zeros n) (Z.to_nat (a - z))) as [b|] eqn:E; [exists b; exact B|].
apply nth_error_None in E. lia.
- apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists (Z_to_bv 8 0). specialize (OK (a - z) ltac:(lia)). replace (z + (a - z)) with a in OK by lia. exact OK.
- apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists (Z_to_bv 8 c). specialize (OK (a - z) ltac:(lia)). replace (z + (a - z)) with a in OK by lia. exact OK.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma known_chunk : forall V m l A n, Forall (mfact_ok asegs V m) l -> 0x5f7000 <= A -> 0 <= n -> A + n <= 2^64 ->
forallb (fun i => mknownb l (A + Z.of_nat i)) (seq 0 (Z.to_nat n)) = true -> wr_at asegs m A n ->
exists j, rw_cells asegs m A [CB (Z.to_nat n) j].
Proof.
intros V m l A n HF H0 H1 H2 HK W.
set (j := map (fun i => match m (wa (A + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
assert (LJ : length j = Z.to_nat n) by (subst j; rewrite length_map, length_seq; reflexivity).
exists j. split; [split|].
- cbn [cells_wf cell_wf]. split; [exact LJ| exact I].
- cbn [cells_bytes cbytes]. rewrite app_nil_r. Local Ltac2 Set LiaHints.tbl := fun () => "0080>1312124725.14 2424890970.14 24931742339.143429177013.18 35727815832.1662091246523.1762091296562.1967340121117.1800000:00A00H00O00V00c010017S2H12H22LJS2H12LJS2H02LJS2LJ2HiS2LJ2HiS2H02H22LJ2HiS2H02H22LJ2HiS2LJ2Hi".
split; [lia|]. split; [rewrite LJ; lia|].
intros i Hi. rewrite LJ in Hi.
pose proof (proj1 (forallb_forall _ _) HK i ltac:(apply in_seq; lia)) as Ki.
destruct (mknown_some V m l (A + Z.of_nat i) HF ltac:(lia) Ki) as [b Hb].
rewrite (mrd_high0 m (A + Z.of_nat i)) by lia. subst j. rewrite nth_error_map, nth_error_seq.
try replace ((i <? Z.to_nat n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
cbn [option_map]. try replace (0 + i)%nat with i by lia. rewrite Hb. reflexivity.
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact W.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition gdesc_cells (b sz swr nm md : Z) : list cell :=
[C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 swr); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615)].
Fixpoint gdescs_imgb (d : Z) (G : list (Z * Z * Z * Z * Z)) : bool :=
match G with
| [] => true
| (b, sz, swr, nm, md) :: G' =>
rw_bytes_b asegs d (cells_bytes (gdesc_cells b sz swr nm md)) && rw_bytes_b asegs (d + 16) [Z_to_bv 8 swr]
&& gdescs_imgb (d + 64) G'
end.
#[using="Type"] Lemma img_chunk_of_none : forall m A cs, cells_wf cs ->
(forall i, A <= i < A + Z.of_nat (cells_size cs) -> m (wa i) = None) ->
rw_bytes_b asegs A (cells_bytes cs) = true -> 0 <= A -> A + Z.of_nat (cells_size cs) <= 2^64 -> rw_cells asegs m A cs.
Proof.
intros m A cs WF R HB HA HHI. pose proof (cells_bytes_length cs WF) as LEN.
eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (cells_bytes cs))| exact WF| cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity| cbn; rewrite LEN, Nat.add_0_r; reflexivity].
- intros a Ha. rewrite <- (Z_to_bv_bv_unsigned a). apply R. rewrite LEN in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>18516291689.12000008S3LEN2Ha".
lia.
- exact HB.
- exact HA.
- rewrite LEN. exact HHI.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gdescs_img_none : forall m G d, (forall i, d <= i < d + 64 * Z.of_nat (length G) -> m (wa i) = None) ->
gdescs_imgb d G = true -> 0 <= d -> d + 64 * Z.of_nat (length G) <= 2^64 -> gdescs m d G.
Proof.
intros m G. induction G as [|[[[[b sz] swr] nm] md] G IH]; intros d R HB H0 H1; cbn [gdescs gdescs_imgb length] in *; [exact I|].
rewrite Nat2Z.inj_succ in R, H1. apply andb_prop in HB as [HB H3]. apply andb_prop in HB as [HB1 HB2].
split; [split|].
- change 18446744073709551615 with (2^64 - 1) in HB1. unfold gdesc_cells in HB1.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>11509201246.1621440833859.1629278692257.162990587486.16 41627462305.1849386019170.165011660081.16 00000400800<00@00D00H00LS2H0S2H1S2H0S2H0S2HiS2H1S2H1".
apply (img_chunk_of_none m d _); [cbn; repeat split; exact I | intros i Hi; apply R; cbn in Hi; lia | exact HB1 | lia | cbn; lia].
- apply (img_chunk_of_none m (d + 16) [C1 (Z_to_bv 8 swr)]); [cbn; tauto | intros i Hi; apply R; cbn in Hi; lia | exact HB2 | lia | cbn; lia].
- apply IH; [intros i Hi; apply R; lia | exact H3 | lia | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma gdescs_img : forall V m l G d, Forall (mfact_ok asegs V m) l ->
existsb (fun f => match f with MImg lo' hi' => (lo' <=? d) && (d + 64 * Z.of_nat (length G) <=? hi') | _ => false end) l = true ->
gdescs_imgb d G = true -> 0 <= d -> d + 64 * Z.of_nat (length G) <= 2^64 -> gdescs m d G.
Proof.
intros V m l G d HF HE HB H0 H1. apply gdescs_img_none; [| exact HB| exact H0| exact H1].
exact (mimg_cover asegs V m l d (d + 64 * Z.of_nat (length G)) HF HE).
Qed.
Section HandoffFacts.
Variables (V : nat -> Z) (m : word -> option byte).
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Let WSH : wr_at asegs m 0x7fffa000 0xbce00.
Proof. mf V m HM (MWr (ZLit 2147459072) 773632) H. exact H. Qed.
#[using="V HM"] Lemma sh_zero1 : forall i, 0 <= i < 8648 -> m (wa (2147459072 + i)) = Some (Z_to_bv 8 0).
Proof. mf V m HM (MZero (ZLit 2147459072) 8648) H. exact H. Qed.
#[using="V HM"] Lemma sh_zero4 : forall i, 0 <= i < 2148232168 - 2148206936 -> m (wa (2148206936 + i)) = Some (Z_to_bv 8 0).
Proof. exact (mzero_cover V m _ 2148206936 (2148232168 - 2148206936) HM ltac:(vm_compute; reflexivity)). Qed.
#[using="V HM WSH"] Lemma fill_chunk : forall A n c,
(forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 c)) -> 0 <= n -> 0x7fffa000 <= A -> A + n <= 0x7fffa000 + 0xbce00 ->
rw_cells asegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].
Proof. intros A n c Hf H2 H4 H5. apply run_rw_cells; [lia| exact Hf| eapply wr_at_sub'; [exact WSH| lia| lia| lia]]. Qed.
#[using="V HM WSH"] Lemma astat_shG : exists j, rw_cells asegs m 0x7fffc1c4 [CB 612 j].
Proof.
apply (known_chunk V m _ 0x7fffc1c4 612 HM); [lia| lia| lia| vm_compute; reflexivity|].
eapply wr_at_sub'; [exact WSH| lia| lia| lia].
Qed.
#[using="V HM WSH"] Lemma astat_shD : exists j, rw_cells asegs m 0x8000bc06 [CB 432 j].
Proof. mf V m HM (MFill (ZLit 2147531782) 432 249) F1. eexists. apply (fill_chunk _ 432 249 F1); lia. Qed.
#[using="V HM"] Lemma gdescs_init : gdescs m 0x9e030 AGLOBALS.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=18845179287.631718793238.6000001002SS".
apply (gdescs_img V m _ AGLOBALS 0x9e030 HM); [vm_compute; reflexivity| vm_compute; reflexivity| lia|].
rewrite AGLOBALS_length. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma atx_stateA0_init : atx_stateA false m.
Proof.
unfold atx_stateA, atx_cellsA, APATX_CALLFN, ACOV_HOOK, APEXIT_GUARD, APAEF_INCB, ACOV_FLAG. cbn [negb].
repeat match goal with |- _ /\ _ => split end.
- Local Ltac2 Set LiaHints.tbl := fun () => "00>0=10067942166.615902553430.616966472342.621930685453.626599019661.629266501014.629760523670.637058847318.650399635789.658563232781.659622971661.662074984214.667170199693.668168776269.600000100200300400500600700800900:00;00<00=00>SSSSSSSSSSSSSS".
aimg V m HM 0x5f5460 [C1 (Z_to_bv 8 0)] H. exact H.
- aimg V m HM 0x5f5464 [C4 (Z_to_bv 64 0)] H. exact H.
- mf V m HM (MCell (ZLit 6247528) 4 (ZLit 1)) H. exact H.
- mf V m HM (MCell (ZLit 6247536) 8 (ZLit 6247544)) H. exact H.
- aimg V m HM 0x5f5478 [C8 (Z_to_bv 64 0)] H. exact H.
- mf V m HM (MCell (ZLit 6247552) 8 (ZLit 561736)) H. exact H.
- mf V m HM (MCell (ZLit 6247808) 8 (ZLit 459764)) H. exact H.
- aimg V m HM 0x5f5488 [C8 (Z_to_bv 64 0)] H. exact H.
- aimg V m HM 0x5f5588 [C8 (Z_to_bv 64 0)] H. exact H.
- aimg V m HM 0x5d4ad4 [C1 (Z_to_bv 8 0)] H. exact H.
- aimg V m HM 0x134320 [C1 (Z_to_bv 8 0)] H. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HM"] Lemma astat_cells :
rw_cells asegs m 0x5d5368 [C4 (Z_to_bv 64 (V 44%nat))]
/\ rw_cells asegs m 0x5f5680 [C4 (Z_to_bv 64 0)]
/\ (exists cdt thr sec tm1, rw_cells asegs m 0x5f56a0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
/\ (exists reg : bool, atx_stateA reg m)
/\ rw_cells asegs m 0x9ee10 [C1 (Z_to_bv 8 0)]
/\ (exists dso, rw_cells asegs m 0x9b480 [C8 dso])
/\ rw_cells asegs m 0x5f5b08 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x9e000 [C8 (Z_to_bv 64 0x9df18)]
/\ rw_cells asegs m 0x9df18 stdin_cells
/\ rw_cells asegs m 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m 0x9de20 [C8 (Z_to_bv 64 RSTDERR)]
/\ rw_cells asegs m 0x9fc90 [C4 (Z_to_bv 64 1)]
/\ rw_cells asegs m 0x9edc0 [C8 (Z_to_bv 64 1)]
/\ rw_cells asegs m 0x9fd30 [C8 (Z_to_bv 64 0)].
Proof.
repeat match goal with |- _ /\ _ => split end.
- mf V m HM (MCell (ZLit 6116200) 4 (ZV 44)) H. exact H.
- Local Ltac2 Set LiaHints.tbl := fun () => "00B0=14382130317.616642273942.620489522317.627460751126.628436747661.628697828237.631394856982.635205724429.640253242902.640255736845.643032133261.644350119901.752877203734.653047290134.655230918285.661905667862.664035091862.667283826310.700000100200300400500600700800900:00;00<00=00>00?00@00A00BSSSSSSSSSSSSSSSSSS".
aimg V m HM 0x5f5680 [C4 (Z_to_bv 64 0)] H. exact H.
- mf V m HM (MCell (ZLit 6248096) 1 (ZLit 1)) H. aimg V m HM 0x5f56a1 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)] H2.
exists (Z_to_bv 8 1), (Z_to_bv 8 0), (Z_to_bv 8 0), (Z_to_bv 64 0).
apply (proj2 (rw_cells_app asegs m 0x5f56a0 [C1 (Z_to_bv 8 1)] _)). split; [exact H| exact H2].
- exists false. exact atx_stateA0_init.
- aimg V m HM 0x9ee10 [C1 (Z_to_bv 8 0)] H. exact H.
- exists (Z_to_bv 64 0x9b480). aimg V m HM 0x9b480 [C8 (Z_to_bv 64 0x9b480)] H. exact H.
- aimg V m HM 0x5f5b08 [C8 (Z_to_bv 64 0)] H. exact H.
- aimg V m HM 0x9e000 [C8 (Z_to_bv 64 0x9df18)] H. exact H.
- unfold stdin_cells. aimg V m HM 0x9df18 [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0x8e660); C8 z64; C8 z64; C8 z64; C8 z64;
C8 (Z_to_bv 64 0x8e68c); C8 z64; C8 (Z_to_bv 64 0x8e7a4); C8 (Z_to_bv 64 0x5f5f28); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)] H. exact H.
- aimg V m HM 0x9df10 [C8 (Z_to_bv 64 RSTDOUT)] H. exact H.
- aimg V m HM 0x9de20 [C8 (Z_to_bv 64 RSTDERR)] H. exact H.
- mf V m HM (MCell (ZLit 654480) 8 (ZLit 72340168526266369)) H. eapply (rw_C8_C4 _ _ _ _ (Z_to_bv 64 0x01010100)); [exact H| apply bytes_eq_of_unsigned; vm_compute; reflexivity].
- mf V m HM (MCell (ZLit 650688) 8 (ZLit 1)) H. exact H.
- mf V m HM (MCell (ZLit 654640) 8 (ZLit 0)) H. exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HandoffFacts.
Section HandoffFacts2.
Variables (V : nat -> Z) (m : word -> option byte).
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Notation usp := (32768 * V 0%nat + (16 * V 6%nat + 4096 * V 10%nat)).
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
#[using="HP"] Lemma tid_range : 1 <= V 44%nat <= 4194303.
Proof. clear HAT. pf V HP (PVar 44 1 4194303) H. exact H. Qed.
#[using="Type"] Lemma sh_sub0 : forall base len lo hi,
(forall i, 0 <= i < len -> m (wa (base + i)) = Some (Z_to_bv 8 0)) ->
base <= lo -> lo <= hi -> hi <= base + len -> 0 <= base -> base + len <= 2^64 ->
shadow_bytes m lo hi (fun _ => 0).
Proof.
clear HAT. intros base len lo hi Hz H1 H2 H3 H4 H5. Local Ltac2 Set LiaHints.tbl := fun () => "0040>29430571884.1552367211439.15589748816.17  768632491.17  00000700>00H00IS2H12H4S2H32H5S2H12H32HsS".
split; [lia|]. split; [lia|]. intros s Hs.
replace s with (base + (s - base)) by lia. apply Hz. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma rodata_sh0_init' : rodata_sh0 m.
Proof.
clear HAT. unfold rodata_sh0.
replace (shad 0x10000) with 2147459072 by reflexivity. replace (shad 0x20de0) with 2147467708 by reflexivity.
split. { apply (sh_sub0 _ _ _ _ (sh_zero1 V m HM)); lia. }
mf V m HM (MWr (ZLit 2147459072) 773632) W. eapply wr_at_sub'; [exact W| lia| lia| lia].
Qed.
#[using="V HM"] Lemma rclean_stdout_buf_init : rclean m RBstdout.
Proof.
clear HAT. unfold RBstdout, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
mf V m HM (MWr (ZLit 2147459072) 773632) W.
replace (shad 0x5f5b00) with 2148232032 by reflexivity. replace (shad 0x5f5f40) with 2148232168 by reflexivity.
Local Ltac2 Set LiaHints.tbl := fun () => "00A0=14495210791.617749361315.618930513671.624854907382.626106365091.627693222819.630322792099.631289978531.634976736358.638452997511.644563438819.644678227207.647465685201.653043097351.656072340643.659635516678.666989014140.600000100200300400500600700800900:00;00<00=00>00?00@00ASSSFSSSSSSSSSSSSS".
split; [| lia]. split; [| split; [| split]].
- eapply (unpoisoned_of_zero m 2148232036 2148232164 (fun _ => 0)); try reflexivity; try lia.
all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
- unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
- eapply wr_at_sub'; [exact W| lia| lia| lia].
- unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma rclean_stage_init : rclean m RSTG.
Proof.
clear HAT. unfold RSTG, rclean, shclean. cbn [r_lo r_hi r_rlo r_rhi].
mf V m HM (MWr (ZLit 2147459072) 773632) W.
replace (shad 0x5c4ac0) with 2148206936 by reflexivity. replace (shad 0x5d4b00) with 2148215136 by reflexivity.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>10143917351.6 14501317127.6 17715739437.1319546713379.6 1998502307.6  22101977507.6 24785556260.6 26351034129.6 26362119843.6 2989503523.6  31473348342.6 33844404899.6 34976736358.6 35991257863.6 38452997511.6 45095694470.6 46476019068.6 48089886883.6 66271788187.6 9921952156.13 00000100200800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00NSSS1H2H0SSSFSSSFSSSSSSSFS1H2H0".
split; [| lia]. split; [| split; [| split]].
- eapply (unpoisoned_of_zero m 2148206936 2148215136 (fun _ => 0)); try reflexivity; try lia.
all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
apply (sh_sub0 _ _ _ _ (sh_zero4 V m HM)); lia.
- unfold hull64, Shadow.KEND. repeat split; try reflexivity; lia.
- eapply wr_at_sub'; [exact W| lia| lia| lia].
- unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma astg_scanZ : AsanHexScan.zscanZ Asan_seg_bytes_003 (ASTAGE - ARepInit_kit.SEG3) 65536 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
#[using="Type"] Lemma astg_scanN : ARepInit_kit.zscanN Asan_seg_bytes_003 64 (Z.to_N (ASTAGE - ARepInit_kit.SEG3)) 65536%N = true.
Proof.
clear.
apply (ARepInit_B.zscanN_complete _ 63); [apply N.leb_le; vm_compute; reflexivity|].
intros i Hi. apply (AsanHexScan.zscanZ_sound _ _ _ astg_scanZ). unfold ASTAGE, ARepInit_kit.SEG3. Local Ltac2 Set LiaHints.tbl := fun () => "0010=65836397480.2000004S2Hi".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma astg_wr_at : wr_at asegs m ASTAGE 65536.
Proof.
clear HAT HM HP V.
unfold ASTAGE. Local Ltac2 Set LiaHints.tbl := fun () => "0070=14501155185.22124235693.5 25759212814.526635829541.529892184720.54179860679.5 46422688303.200000100500900=00A00E00FSS2HiS2HiS2HiS2HiS2HiS".
split; [lia|]. split; [lia|]. intros i Hi. unfold wview.
destruct (m (wa (0x5c4ad0 + i))) as [b|] eqn:E; [discriminate|].
rewrite wa_unsigned by lia. rewrite (ARepInit_kit.a_find_segment_3 (0x5c4ad0 + i)) by lia.
replace (seg_writable Asan_segment_003) with true by (vm_compute; reflexivity).
rewrite ARepInit_kit.seg3_base.
cbn [seg_bytes Asan_segment_003 segment_byte_at]. rewrite ARepInit_kit.seg3_chunk_bytes.
replace (Z.to_N (0x5c4ad0 + i - 0x9b000) <? 0x55c000)%N with true by (symmetry; apply N.ltb_lt; lia).
replace (Z.to_N (0x5c4ad0 + i - 0x9b000)) with (Z.to_N (0x5c4ad0 - 0x9b000) + Z.to_N i)%N by lia.
rewrite (ARepInit_kit.zscanN_sound _ 64 _ 65536%N astg_scanN (Z.to_N i)) by lia. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma astg_init : ASTG m.
Proof.
clear HAT. exists (repeat (Z_to_bv 8 0) ASTAGE_LEN).
Local Ltac2 Set LiaHints.tbl := fun () => "0050=18928857998.518930743321.631729603869.637788979786.650967081992.800000100400700:00@SS1ES1ES1ES1E2Hi".
assert (E : ASTAGE_LEN = Z.to_nat 65536) by (apply Nat2Z.inj; rewrite ASTAGE_LEN_Z, Z2Nat.id by lia; reflexivity).
rewrite E.
apply (ARepInit_kit.img_zero_cells (Z.to_N (ASTAGE - ARepInit_kit.SEG3)) 65536%N m ASTAGE).
- exact astg_scanN.
- reflexivity.
- unfold ASTAGE. lia.
- intros i Hi. apply (mimg_cover asegs V m _ 6048458 6116160 HM); [vm_compute; reflexivity| unfold ASTAGE in Hi; lia].
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact astg_wr_at.
- vm_compute. reflexivity.
- cbn [cells_size csize]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V HM"] Lemma atrun_cells0_init' : rw_cells asegs m 0x5d4ad0 [C1 (Z_to_bv 8 0)].
Proof. clear HAT. aimg V m HM 0x5d4ad0 [C1 (Z_to_bv 8 0)] H. exact H. Qed.
#[using="HM"] Lemma stage2_word_init : bytes_at asegs m (usp + -8) (le8 z64).
Proof.
clear HAT. mf V m HM (MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)) H.
apply rw_cells_bytes_at in H. cbn [cells_bytes cbytes app] in H. rewrite app_nil_r in H. exact H.
Qed.
#[using="HM"] Lemma argv_ptrs_init :
bytes_at asegs m (usp + 8) (word_to_le_bytes 8 (Z_to_bv 64 (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (16 * V 6%nat + 4096 * V 10%nat))) + 184)))
/\ bytes_at asegs m (usp + 16) (word_to_le_bytes 8 (Z_to_bv 64
(Z.b2z ((1 mod two64) <? (V 1%nat mod two64)) * (32768 * V 0%nat + (8 * V 1%nat + (8 * V 2%nat + (V 3%nat + (16 * V 6%nat + 4096 * V 10%nat)))) + 185)))).
Proof.
clear HAT. split.
- mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))) H. exact H.
- mf V m HM (MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))) H. exact H.
Qed.
#[using="V HM HP HAT"] Lemma stack_shclean_init : forall lo hi RLO RHI,
ATOP <= RLO -> RLO <= lo -> lo < hi -> hi <= RHI -> hi + 8 <= KEND -> RHI <= KEND -> RLO mod 64 = 0 -> RHI mod 64 = 0 ->
shclean m lo hi RLO RHI.
Proof.
intros lo hi RLO RHI H1 H2 H3 H4 H5 H5' H6 H7. unfold KEND in *.
pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
mf V m HM (MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
(ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) W0.
mf V m HM (MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304))
(ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))) ZW.
assert (W : wr_at asegs m (shad ATOP) (17594333495296 - shad ATOP)).
{ rewrite shad_div. unfold AsanEmbed.ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>12172789927.5918179156467.2420317223033.2425606868576.1425608965479.4526789534638.5227887488890.5229432667347.2429871633935.2431205687274.4 31792762540.2444289299384.2445023101068.2448419127702.2451389708122.1452365100048.2454584852053.1462475106010.2465235075244.4567703711251.528043047137.52 8444202024.16 00000=00C00D00Q00i01201C01L01Q01R01V01Z01l02>02K02O02P02Y02Z02[03603FS3H5'3H113H12S2H11HFS3HAT1H2H02H4S3HAT1H2H03H212H12H63H16S2H51H2H0S2H31H2H03H113H12S2H12H21HS3H5'SS2H2S2H4S2H12H22H32H42H71HS2H12H22H32H42H51HS3HAT2P61H2H0S2H5SS2H12H61HSFS2H12H21H2H03H113H122H63H21S3HAT2P62Hi1H2H0".
eapply wr_at_sub'; [exact W0| | |]; clear - HAT P0 P6 P10; Z.div_mod_to_equations; lia. }
assert (ZR : forall i, 0 <= i < 17594333495296 - shad ATOP -> m (wa (shad ATOP + i)) = Some (Z_to_bv 8 0)).
{ intros i Hi. rewrite shad_div in Hi |- *. unfold AsanEmbed.ASHOFF in Hi |- *.
match goal with |- m (wa ?a) = _ =>
replace a with (4096 * V 0%nat + 512 * V 10%nat + 2146402304 + (a - (4096 * V 0%nat + 512 * V 10%nat + 2146402304))) by (clear; lia) end.
apply ZW. clear - HAT P0 P6 P10 Hi. Z.div_mod_to_equations. lia. }
clear W0 ZW.
split; [| split; [| split]].
- eapply (unpoisoned_of_zero m (shad lo) (shad (hi - 1) + 1) (fun _ => 0)); try reflexivity; try lia.
all: try (rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia).
apply (sh_sub0 _ _ _ _ ZR); rewrite ?shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia.
- unfold hull64, Shadow.KEND. repeat split; lia.
- eapply wr_at_sub'; [exact W| ..]; rewrite !shad_div; unfold AsanEmbed.ASHOFF; Z.div_mod_to_equations; lia.
- unfold app_blk, Shadow.KLOW, Shadow.KHIGH, Shadow.KEND. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End HandoffFacts2.
#[using="Type"] Lemma firstn_add_split : forall {A} (a b : nat) (l : list A), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
intros A a b l. revert l. induction a as [|a IH]; intros l; [reflexivity|].
destruct l as [|x l]; cbn; [destruct b; reflexivity| f_equal; apply IH].
Qed.
#[using="Type"] Lemma bytes_at_agree : forall (m m' : word -> option byte) a bs,
bytes_at asegs m a bs -> (forall z, a <= z < a + Z.of_nat (length bs) -> m' (wa z) = m (wa z)) -> bytes_at asegs m' a bs.
Proof.
intros m m' a bs (A & B & H) AG. split; [exact A|]. split; [exact B|]. intros i Hi.
unfold mrd. Local Ltac2 Set LiaHints.tbl := fun () => "0010>53024458931.11000004S2Hi".
rewrite (AG (a + Z.of_nat i)) by lia. apply (H i Hi).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section StringBlock.
Variables (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : word -> option byte).
Notation usp := (bv_unsigned sp).
Notation m0 := (wrap_mem a_phdrs sp argv envp uid hw draw).
Definition SBLK : list byte := flatten_strings argv ++ flatten_strings envp ++ repeat (Z_to_bv 8 0) (Z.to_nat (pad_len argv envp)).
Notation SB := (str_base sp argv envp).
#[using="Type"] Lemma SBLK_length : Z.of_nat (length SBLK) = total_arg_bytes argv + total_arg_bytes envp + pad_len argv envp.
Proof.
unfold SBLK. rewrite !length_app, repeat_length. pose proof (flatten_strings_length argv). pose proof (flatten_strings_length envp).
pose proof (raw_len_nonneg argv envp). Local Ltac2 Set LiaHints.tbl := fun () => "0010>30555039533.11000009S1H2H02H1".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Hypothesis SPLO : stack_max_size <= usp.
Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image a_phdrs sp argv envp uid hw draw)) <= 2^64.
Hypothesis SP16 : usp mod 16 = 0.
Hypothesis VARGV : valid_argv argv.
Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length SBLK) -> m (wa z) = m0 (wa z).
#[using="SP16"] Lemma SBLK_mod8 : (SB + Z.of_nat (length SBLK)) mod 8 = 0 /\ SB mod 8 = 0.
Proof.
clear SPLO IMGHI VARGV HID. rewrite SBLK_length. unfold str_base, struct_size, pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc.
pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4). unfold struct_size, Lib.InitMem.argc, Lib.InitMem.envc in R1.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>66149329538.4166151427842.2700000E00SS4SP161H2H02H42H93H14S4SP161H2H02H4".
split; Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="uid hw draw SPLO IMGHI HID"] Lemma SBLK_at : bytes_at asegs m SB SBLK.
Proof.
eapply bytes_at_agree; [| exact HID].
pose proof (init_stack_bytes asegs a_phdrs sp argv envp uid hw draw SPLO IMGHI) as B. rewrite build_stack_bytes_eq in B.
unfold raw_bytes in B. set (U := u64s _) in B. set (FA := flatten_strings argv) in B. set (FE := flatten_strings envp) in B.
set (PAD := repeat _ _) in B. set (RND := rnd_bytes draw) in B.
replace ((U ++ FA ++ FE) ++ PAD ++ RND) with (U ++ ((FA ++ FE ++ PAD) ++ RND)) in B by (rewrite <- !app_assoc; reflexivity).
apply bytes_at_app in B. destruct B as [_ B]. apply bytes_at_app in B. destruct B as [B _].
assert (LU : Z.of_nat (length U) = struct_size argv envp).
{ subst U. rewrite u64s_length. cbn [length]. rewrite !length_app. cbn [length].
unfold argv_ptrs, envp_ptrs. rewrite !map_length, !str_ptrs_length.
match goal with |- context [length (auxv_words ?a ?b ?c ?d ?e ?f)] => change (length (auxv_words a b c d e f)) with 20%nat end.
unfold struct_size, Lib.InitMem.argc, Lib.InitMem.envc. Local Ltac2 Set LiaHints.tbl := fun () => "0020>31250298448.1765955603401.18000004005S2LUS".
lia. }
unfold SBLK. subst FA FE PAD. replace SB with (usp + Z.of_nat (length U)); [exact B|].
unfold str_base. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="uid hw draw SPLO IMGHI SP16 HID"] Lemma arg_string : forall i s, nth_error argv i = Some s ->
exists off, nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off /\
let P := SB + off in
let k := (- (P + Z.of_nat (length s) + 1)) mod 8 in
exists slack : list byte, zlength slack = k /\ P + Z.of_nat (length s) + 1 + k <= SB + Z.of_nat (length SBLK)
/\ bytes_at asegs m P (s ++ Z_to_bv 8 0 :: slack).
Proof.
intros i s Hn. destruct (str_ptrs_nth argv SB i s Hn) as (off & Hp & Ho & Ht & Hf).
exists off. split; [exact Hp|]. split; [exact Ho|]. cbv zeta.
pose proof SBLK_mod8 as [M1 M2]. pose proof SBLK_length as SL. pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4).
set (k := (- (SB + off + Z.of_nat (length s) + 1)) mod 8).
Local Ltac2 Set LiaHints.tbl := fun () => "0070>13714664255.3215200645030.3319033648627.5623230617938.3437466247107.314504959674.33 57988272893.3200000>00B00F00c01:01A01ES2Ho2Hk3FIT2LSS2LSS2H0S2Ho2Ht2SL2R32R42Hk3FIT2LS2FLS2Ho2Ht2SL2R32R42Hk3FITS2Ho2LSS2LS".
assert (Hk : 0 <= k < 8) by (subst k; Z.div_mod_to_equations; lia).
assert (FIT : SB + off + Z.of_nat (length s) + 1 + k <= SB + Z.of_nat (length SBLK)).
{ subst k. Z.div_mod_to_equations. nia. }
exists (firstn (Z.to_nat k) (skipn (Z.to_nat off + (length s + 1)) SBLK)).
assert (LS : (Z.to_nat off + (length s + 1) + Z.to_nat k <= length SBLK)%nat) by lia.
split. { unfold zlength. rewrite firstn_length, length_skipn. lia. }
split; [exact FIT|].
pose proof (bytes_at_slice asegs a_phdrs sp argv envp uid hw draw m SB SBLK (Z.to_nat off) (length s + 1 + Z.to_nat k) SBLK_at ltac:(lia)) as B.
rewrite Z2Nat.id in B by lia. rewrite firstn_add_split in B. rewrite skipn_skipn in B || rewrite <- skipn_add in B || idtac.
eapply bytes_at_ext; [exact B|].
replace (length s + 1 + Z.to_nat off)%nat with (Z.to_nat off + (length s + 1))%nat by lia.
replace (firstn (length s + 1) (skipn (Z.to_nat off) SBLK)) with (s ++ [Z_to_bv 8 0]); [rewrite <- app_assoc; reflexivity|].
symmetry. unfold SBLK. rewrite skipn_app, firstn_app.
pose proof (flatten_strings_length argv) as FL.
rewrite Hf. rewrite length_skipn.
replace (length s + 1 - (length (flatten_strings argv) - Z.to_nat off))%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End StringBlock.
End CANSEC4.
Ltac lit_divs := repeat match goal with |- context [?a / ?b] =>
let v := eval vm_compute in (a / b) in lazymatch v with Zpos _ => change (a / b) with v | Z0 => change (a / b) with v end end.
Section CANSEC5. Context {rc : runConstT}.
Section VisRng.
Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z).
Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
#[using="Type"] Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
Proof.
clear A0I HP HAT. intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>61116987935.13000009S2Hz1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="A0I"] Lemma vis_rng_gen : forall b n lo len,
In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
rng (fp_ok lz AL) lo len.
Proof.
clear HP HAT. intros b n lo len HIN H1 H2 H3 H4. Local Ltac2 Set LiaHints.tbl := fun () => "0040>14664690553.1417260316074.3129430571759.1438557618280.1600000400;00?00IS2H4S2H82H9S2H3S2H32H42Hz".
apply rng_fp_ok_allowed; [lia| lia|].
intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->
In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
/\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
Proof.
clear A0I HP HAT. intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
Qed.
#[using="A0I"] Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.
#[using="A0I"] Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
rng (fp_ok lz AL) lo len.
Proof.
clear HP HAT. intros k bn lo len Hk H1 H2 H3 H4.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>1168424123.14 14664690553.1421409089299.1429430571759.145113183001.14 00000100500900=00ASS2H4S2H2S2H3S2H1".
eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8));
[| lia| lia| lia| lia].
replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
exact (proj2 (allow_in_app k bn Hk)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V A0I"] Lemma rng_image : forall lo len, 0x10000 <= lo -> lo + len <= 0x5f7000 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
#[using="V A0I"] Lemma rng_image_sh : forall lo len, 0x7fffa000 <= lo -> lo + len <= 0x800b6e00 -> rng (fp_ok lz AL) lo len.
Proof. clear HP HAT. intros lo len H1 H2. eapply (vis_rng_sh 11); [reflexivity| cbn; lit_divs; lia| cbn; lit_divs; lia| lia| lia]. Qed.
#[using="V A0I HP HAT"] Lemma rng_stackside : forall lo len, ATOP <= lo -> lo + len <= 2^47 -> rng (fp_ok lz AL) lo len.
Proof.
intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
eapply (vis_rng 12); [reflexivity| cbn; lia| cbn; lia| lia| lia].
Qed.
#[using="V A0I HP HAT"] Lemma rng_stackside_sh : forall lo len, shad ATOP <= lo -> lo + len <= 17594333495296 -> rng (fp_ok lz AL) lo len.
Proof.
intros lo len H1 H2. atop_facts. pf V HP (PVar 0 4294901760 4294967295) P0. pf V HP (PVar 6 0 255) P6. pf V HP (PVar 10 0 7) P10.
rewrite shad_div in H1. unfold AsanEmbed.ASHOFF in H1.
eapply (vis_rng_sh 12); [reflexivity| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| cbn -[Z.div Z.mul Z.add]; Z.div_mod_to_equations; lia| lia| lia].
Qed.
#[using="A0I"] Lemma rng_fake : forall (P393 : 4096 <= 4096 * V 377%nat /\ 4096 * V 377%nat + 11571200 <= ATOP),
rng (fp_ok lz AL) (4096 * V 377%nat) 11571200 /\ rng (fp_ok lz AL) (shad (4096 * V 377%nat)) (shlen 11571200).
Proof.
clear HP HAT. intros P393. atop_facts. split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0090>1032234420.7  28212098390.7 29782367974.7 32304748391.7 37160815576.7 43241202387.2848142679296.7 61965584229.2167251438280.7 00000100700800>00?00T00\010011SS4P393SS4P393SS2H02H12H52H63H103H11S4P3931HS4P3931H2H02H12H52H6S".
eapply (vis_rng 3); [reflexivity| cbn; lia| cbn; lia| lia| lia].
- rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
eapply (vis_rng_sh 3); [reflexivity| cbn -[Z.div Z.mul]; lia| cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia| lia| Z.div_mod_to_equations; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="A0I"] Lemma rng_dtls : forall (P310 : 4096 <= 4096 * V 310%nat /\ 4096 * V 310%nat + 4096 <= ATOP), rng (fp_ok lz AL) (4096 * V 310%nat) 4096.
Proof. clear HP HAT. intros P310. atop_facts. eapply (vis_rng 4); [reflexivity| cbn; lia| cbn; lia| lia| lia]. Qed.
#[using="Type"] Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng (fp_ok lz AL) b 0.
Proof. clear A0I HP HAT. intros b Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0030=33629942853.861883801886.68739886716.6 00000400800<S2HzS2HbS2Hb".
apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End VisRng.
Section ArgPack.
Variables (V : nat -> Z) (sp : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (m : word -> option byte).
Notation usp := (bv_unsigned sp).
Notation SB := (str_base sp argv envp).
Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis SPLO : stack_max_size <= usp.
Hypothesis IMGHI : usp + Z.of_nat (length (entry_stack_image a_phdrs sp argv envp uid hw draw)) <= 2^64.
Hypothesis SP16 : usp mod 16 = 0.
Hypothesis SPW : ATOP + 8388608 <= usp.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Hypothesis FITS : usp + entry_stack_span argv envp <= 2^47.
Hypothesis VARGV : valid_argv argv.
Hypothesis HID : forall z, SB <= z < SB + Z.of_nat (length (SBLK argv envp)) -> m (wa z) = wrap_mem a_phdrs sp argv envp uid hw draw (wa z).
Definition round_dn64 (x : Z) : Z := x / 64 * 64.
Definition round_up64 (x : Z) : Z := (x + 63) / 64 * 64.
#[using="rc VARGV"] Lemma span_ge : SB + Z.of_nat (length (SBLK argv envp)) + 16 <= usp + entry_stack_span argv envp /\ usp + 192 <= SB.
Proof.
clear HM HP SPLO IMGHI SP16 SPW FITS HID. rewrite SBLK_length. unfold str_base, struct_size, Lib.InitMem.argc, Lib.InitMem.envc, entry_stack_span, pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc.
pose proof (raw_len_nonneg argv envp) as (R1 & R2 & R3 & R4). unfold pad_len, raw_len, struct_size, Lib.InitMem.argc, Lib.InitMem.envc in R4.
destruct VARGV as (A1 & _). change (Z.of_nat auxv_size) with 160.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>19770166445.1720724056121.3100000:00>S2R22R32A1S2R4".
split; [| lia]. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="V uid hw draw HM HP SPLO IMGHI SP16 SPW HAT FITS VARGV HID"] Lemma arg_pack : forall i s, nth_error argv i = Some s ->
exists off (slack : list byte) (r : region),
nth_error (str_ptrs SB argv) i = Some (SB + off) /\ 0 <= off
/\ bytes_at asegs m (SB + off) (s ++ Z_to_bv 8 0 :: slack)
/\ (- (SB + off + Z.of_nat (length s) + 1)) mod 8 <= zlength slack
/\ usp + 24 <= SB + off
/\ shclean m (r_lo r) (r_hi r) (r_rlo r) (r_rhi r) /\ r_lo r < r_hi r
/\ inreg r (SB + off) (Z.of_nat (length s) + 1 + zlength slack)
/\ usp + -112 <= r_rlo r /\ ATOP <= r_rlo r /\ r_rhi r <= 2^47
/\ SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47.
Proof.
intros i s Hn.
destruct (arg_string sp argv envp uid hw draw m SPLO IMGHI SP16 HID i s Hn) as (off & Hp & Ho & slack & SL & FIT & BY).
cbv zeta in SL, FIT.
pose proof span_ge as [SG1 SG2]. pose proof (SBLK_mod8 sp argv envp SP16) as [M1 M2]. atop_facts.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>10433973477.3810746855567.381607278993.38 16936740393.3821263250465.3827609915065.3832749706502.8632749706889.783665281493.38 38309828691.3438569593740.354511089163.38 4724217088.38 49722223811.3850189981417.3859014471979.3862504773662.3863463036573.386425729787.38 9063849466.38 00000400500900S00T00n01E01R01S01T01o02302M02Q02k02o03I03M03g03kS2U1SS2HES3SPW2Ho2SL3SG21H2LS2D12U1SS3SPW2Ho2SL3SG21H2LS2D12U1S2SL2HE2H02H12H52H63H25S2H02H12H52H6FSS3SPW4FITS2SL3FIT3SG13SG21HS2HoS3SPW2Ho2SL3SG21H2LS2D12U1S2U1S3SPW2Ho2SL3SG21H2LS2D12U1S2HES3SPW2Ho2SL3SG21H2LS2D12U1S2D1S3SPW2Ho2SL3SG21H2LS2D12U1S2U1".
assert (LS : 0 <= zlength slack) by (unfold zlength; lia).
assert (HE : SB + off + Z.of_nat (length s) + 1 + zlength slack <= 2^47 - 16) by lia.
assert (D1 : SB + off - 63 <= round_dn64 (SB + off) <= SB + off /\ round_dn64 (SB + off) mod 64 = 0) by (unfold round_dn64; Z.div_mod_to_equations; lia).
assert (U1 : SB + off + Z.of_nat (length s) + 1 + zlength slack <= round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) <= 2^47
/\ round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack) mod 64 = 0) by (unfold round_up64; Z.div_mod_to_equations; lia).
exists off, slack, (mkRegion (SB + off) (SB + off + Z.of_nat (length s) + 1 + zlength slack)
(round_dn64 (SB + off)) (round_up64 (SB + off + Z.of_nat (length s) + 1 + zlength slack))).
cbn [r_lo r_hi r_rlo r_rhi]. unfold inreg. cbn [r_lo r_hi].
repeat match goal with |- _ /\ _ => split end; try exact Hp; try exact BY; try lia.
apply (stack_shclean_init V m HM HP HAT); unfold Shadow.KEND; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End ArgPack.
End CANSEC5.
