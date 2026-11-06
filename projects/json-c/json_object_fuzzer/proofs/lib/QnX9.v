(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Section Cells.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_pair : forall m A x y,
rw_cells segs m A [C1 x] -> rw_cells segs m (A + 1) [C1 y] -> rw_cells segs m A [C1 x; C1 y].
Proof. intros m A x y H1 H2. apply (proj2 (rw_cells_app segs m A [C1 x] [C1 y])). split; [exact H1 | exact H2]. Qed.

#[using="Type"] Lemma rw_cells_unpair : forall m A x y,
rw_cells segs m A [C1 x; C1 y] -> rw_cells segs m A [C1 x] /\ rw_cells segs m (A + 1) [C1 y].
Proof. intros m A x y H. apply (proj1 (rw_cells_app segs m A [C1 x] [C1 y])) in H. exact H. Qed.

#[using="Type"] Lemma rw_cells_CB_snoc : forall m A n s b,
rw_cells segs m A [CB n s] -> rw_cells segs m (A + Z.of_nat n) [C1 b] -> rw_cells segs m A [CB (S n) (s ++ [b])].
Proof.
intros m A n s b H1 H2.
assert (L : length s = n) by (destruct H1 as [[[Hwf _] _] _]; exact Hwf).
assert (H : rw_cells segs m A ([CB n s] ++ [C1 b])).
{ apply (proj2 (rw_cells_app segs m A [CB n s] [C1 b])). cbn [cells_size csize]. rewrite Nat.add_0_r. split; [exact H1 | exact H2]. }
eapply rw_cells_recast; [exact H | cbn; rewrite length_app; cbn; lia | cbn; rewrite app_nil_r; reflexivity | cbn; lia].
Qed.

#[using="Type"] Lemma rw_cells_CB_head : forall m A n b bs,
rw_cells segs m A [CB (S n) (b :: bs)] -> rw_cells segs m A [C1 b] /\ rw_cells segs m (A + 1) [CB n bs].
Proof.
intros m A n b bs H.
destruct (rw_cells_CB_cut segs m A (S n) (b :: bs) 1 H ltac:(lia)) as [H1 H2].
cbn [firstn skipn] in H1, H2. change (Z.of_nat 1) with 1 in H2. replace (S n - 1)%nat with n in H2 by lia.
split; [| exact H2].
eapply rw_cells_recast; [exact H1 | cbn; split; exact I | reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma obj_join : forall m S n (szb j : byte) s rest,
0 <= n <= 21 -> bv_unsigned szb = 2 * n ->
rw_cells segs m S [C1 szb] ->
rw_cells segs m (S + 1) [CB (Z.to_nat n) s] ->
rw_cells segs m (S + n + 1) [C1 b0; C1 j] ->
rw_cells segs m (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells segs m S [C1 (Z_to_bv 8 (2 * n)); CB 23 (s ++ b0 :: j :: rest)].
Proof.
intros m S n szb j s rest Hn Hsz SZ DATA WIN REST.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
pose proof (rw_cells_bound segs _ _ _ REST) as B. cbn [cells_size csize Nat.add] in B.
assert (H : rw_cells segs m S ([C1 szb] ++ ([CB (Z.to_nat n) s] ++ ([C1 b0; C1 j] ++ [CB (Z.to_nat (21 - n)) rest])))).
{ apply (proj2 (rw_cells_app segs m S _ _)). split; [exact SZ|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 1) with 1.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact DATA|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. replace (S + 1 + n) with (S + n + 1) by lia.
apply (proj2 (rw_cells_app segs m _ _ _)). split; [exact WIN|]. cbn [cells_size csize Nat.add]. change (Z.of_nat 2) with 2.
replace (S + n + 1 + 2) with (S + n + 3) by lia. exact REST. }
eapply rw_cells_recast; [exact H | | |].
- cbn [cells_wf cell_wf csize length]. rewrite length_app. cbn [length].
repeat split; try exact I; try reflexivity. lia.
- cbn. rewrite <- app_assoc. cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 (2 * n)) with ((2 * n) mod 2 ^ 8).
pose proof (bv_unsigned_in_range 8 szb) as R. unfold bv_modulus in R. cbn in R. rewrite Z.mod_small; lia.
- cbn. lia.
Qed.
End Cells.

Lemma first_nul_split : forall (pre post : list byte),
exists str rest, pre ++ b0 :: post = str ++ b0 :: rest /\ ~ In b0 str /\ (length str <= length pre)%nat.
Proof.
induction pre as [|b pre IH]; intros post.
- exists [], post. split; [reflexivity|]. split; [intros H; exact H | cbn; lia].
- destruct (Z.eq_dec (bv_unsigned b) 0) as [E|NE].
+ exists [], (pre ++ b0 :: post). split; [| split; [intros H; exact H | cbn; lia]].
change (b :: (pre ++ b0 :: post) = b0 :: (pre ++ b0 :: post)). f_equal. apply bv_eq. rewrite E. reflexivity.
+ destruct (IH post) as (str & rest & E2 & Hn & Hl). exists (b :: str), rest.
split; [change (b :: (pre ++ b0 :: post) = b :: (str ++ b0 :: rest)); rewrite E2; reflexivity|].
split; [| cbn; lia]. intros [H|H]; [| exact (Hn H)]. apply NE. rewrite H. reflexivity.
Qed.

Lemma lor7_eq23 : forall n, 16 <= n <= 23 -> Z.lor n 7 = 23.
Proof.
intros n Hn.
assert (H : forallb (fun k => Z.lor (16 + Z.of_nat k) 7 =? 23) (seq 0 8) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat (n - 16)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq in H. replace (16 + (n - 16)) with n in H by lia. exact H.
Qed.
Lemma lor7_bound : forall n, 0 <= n <= 15 -> 7 <= Z.lor n 7 <= 15.
Proof.
intros n Hn.
assert (H : forallb (fun k => andb (7 <=? Z.lor (Z.of_nat k) 7) (Z.lor (Z.of_nat k) 7 <=? 15)) (seq 0 16) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H (Z.to_nat n) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply andb_true_iff in H as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Tactic Notation "call_pushb" constr(Sv) constr(nv) constr(lov) constr(szbv) constr(xv) constr(yv) :=
lazymatch goal with
| |- evt _ _ (MS (TNode _ None (TNode _ (Some (Z_to_bv 64 (bv_unsigned ?sp + ?k))) _)) _ _ _ _ _ _) => name_sp sp k
| |- evt _ _ (MS (mkR _ (Z_to_bv 64 (bv_unsigned ?sp + ?k)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => name_sp sp k
end;
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply pushb_spec with (S := Sv) (n := nv) (lo := lov) (szb := szbv) (x := xv) (y := yv)
| unfold pushb_post, pushb_W; post_call segs mm] end;
unname_sp.

Lemma neq_wz : forall x y, 0 <= x < 2^64 -> -2^64 <= y < 2^64 -> x <> y -> x <> y + 2^64 ->
bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
intros x y Hx Hy N1 N2. unfold bv_eqb. apply Z.eqb_neq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
destruct (Z.lt_ge_cases y 0).
- replace y with ((y + 2^64) + (-1) * 2^64) at 1 by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
- rewrite Z.mod_small by lia. lia.
Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section ACrls.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET_U : amemset_spec_U.

Definition CRLS_STK_B : Z := 160 + 4096.

Definition crls_presB (S P : Z) (LB : list blk) (SP : Z) (m m' : word -> option byte) : Prop :=
forall a, 0 <= a < 2^64 -> client_addr A4H LB SP a -> ~ (S <= a < S + 24) -> ~ (P <= a < P + 16) ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

Definition crls_WB (lo sp P S Fr : Z) : list (Z * Z) := [(lo, sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (Fr / 8 + 2147450880, Fr / 8 + 2147450880 + 8)].

Lemma crls_fk_HEAPA : forall A LB LM FRS B m md Fr lo sp P S mX,
HEAPAx A LB LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> lo <= sp -> sp <= hiA_top A4L HIx -> arg_locA FRS P 16 -> arg_locA FRS S 24 ->
munch (crls_WB lo sp P S Fr) m mX -> wmono asegs m mX -> mem_inv asegs mX -> HEAPAx A LB LM ((Fr, 0) :: FRS) B mX md.
Proof.
intros A LB LM FRS B m md Fr lo sp P S mX HP LO LSP SHT (Fp & kp & HFp & HPlo & HPhi) (Fc & kc & HFc & HSlo & HShi) MU WM MI.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU). unfold crls_WB.
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
- left. cbn [fst snd]. lia.
- right; right; right. exists Fp, kp. split; [right; exact HFp|]. left. cbn [fst snd]. lia.
- right; right; right. exists Fc, kc. split; [right; exact HFc|]. left. cbn [fst snd]. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_0. unfold A_SB. lia.
Qed.

Lemma nodup_cons_notin : forall (X : Type) (x : X) (l : list X), NoDup (x :: l) -> ~ In x l.
Proof. intros X x l H Hin. inversion H as [| y l' NI ND]. apply NI. apply list_elem_of_In. exact Hin. Qed.

Lemma crls_fk_pres : forall A LB LM FRS B m md Fr lo sp P S mX,
HEAPAx A LB LM ((Fr, 0) :: FRS) B m md -> alloc_ceiling <= lo -> lo <= sp ->
munch (crls_WB lo sp P S Fr) m mX -> wmono asegs m mX ->
crls_presB S P (LB ++ LM ++ fr_ivs A4L FRS) sp m mX.
Proof.
intros A LB LM FRS B m md Fr lo sp P S mX HP LO LSP MU WM a Ha CA NS NP.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFrc & HFimg & _). rewrite fr_size_0 in HFrc, HFal, HFimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp. rewrite fr_size_0 in HFapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFapp.
pose proof alloc_ceiling_range as ACR.
assert (OUT : outside (crls_WB lo sp P S Fr) a).
2:{ split; [rewrite <- (wa_unsigned a) in OUT by lia; apply MU; exact OUT | intros Hw; exact (WM _ Hw)]. }
unfold crls_WB. cbn [outside].
destruct CA as [Hsp | [Hcs | (b & Hb & Hr)]].
- repeat split; try lia; try exact I. all: clear - Hsp Ha LO LSP ACR HFrc HF0; Z.div_mod_to_equations; nia.
- cbn [hl_client_static A4H hla_base] in Hcs. unfold a4_client_static in Hcs.
repeat split; try lia; try exact I. all: clear - Hcs HFimg Ha ACR LO HF0 HFrc; Z.div_mod_to_equations; nia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
+ pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hb) as DF. rewrite fr_size_0 in DF.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP Hb) as (_ & _ & Hb0 & Hbc & _).
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ba bn HP Hb) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
repeat split; try lia; try exact I. all: clear - DF Hb0 Hbc APP Hr Ha ACR LO HF0 HFrc; Z.div_mod_to_equations; nia.
+ apply QSHS.in_fr_ivs in Hb as (Fc & kc & HFc & Hbk).
assert (NE : Fr <> Fc).
{ intros E. pose proof (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. cbn [map fr_base fst] in ND.
apply (nodup_cons_notin _ _ _ ND). rewrite E. apply in_map_iff. exists (Fc, kc). split; [reflexivity | exact HFc]. }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF (or_intror HFc) NE) as AP. rewrite fr_size_0 in AP.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFc)) as (Hkc & HFcal & HFc0 & HFcc & _ ).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFc)) as HFcapp. cbn [hl_sb A4L] in HFcapp. unfold A_SB in HFcapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFcapp.
pose proof (QSHS.fr_size_pos kc ltac:(lia)) as FSP.
destruct Hbk as [E | E]; apply pair_equal_spec in E as [-> ->].
* repeat split; try lia; try exact I. all: clear - AP Hr Ha ACR LO HF0 HFrc HFc0 HFcc FSP; Z.div_mod_to_equations; nia.
* unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in Hr. rewrite (QSHS.fr_size_shadow kc) in AP, HFcc, HFcapp by lia.
repeat split; try lia; try exact I. all: clear - AP Hr Ha ACR LO HF0 HFrc HFc0 HFcc FSP HFapp HFcapp HFal; Z.div_mod_to_equations; nia.
Qed.

Lemma presB_trans : forall S P LBX sp m m' m'', crls_presB S P LBX sp m m' -> crls_presB S P LBX sp m' m'' -> crls_presB S P LBX sp m m''.
Proof.
intros S P LBX sp m m' m'' H1 H2 a Ha CA NS NP. destruct (H1 a Ha CA NS NP) as [E1 W1]. destruct (H2 a Ha CA NS NP) as [E2 W2].
split; [rewrite E2; exact E1 | intros Hw; exact (W2 (W1 Hw))].
Qed.

Lemma presB_heap_pres : forall S P LBX SP sp m m', heap_pres A4H LBX SP m m' -> SP <= sp -> crls_presB S P LBX sp m m'.
Proof.
intros S P LBX SP sp m m' HPR LE a Ha CA NS NP. apply (HPR a Ha).
destruct CA as [H | [H | H]]; [left; lia | right; left; exact H | right; right; exact H].
Qed.

Lemma presB_stack : forall A LB LM FRS B m md lo sp m1 S P,
HEAPAx A LB LM FRS B m md -> alloc_ceiling <= lo -> munch [(lo, sp)] m m1 -> wmono asegs m m1 ->
crls_presB S P (LB ++ LM ++ fr_ivs A4L FRS) sp m m1.
Proof.
intros A LB LM FRS B m md lo sp m1 S P HP LO MU WM a Ha CA NS NP. pose proof alloc_ceiling_range as ACR.
assert (OUT : outside [(lo, sp)] a).
2:{ split; [rewrite <- (wa_unsigned a) in OUT by lia; apply MU; exact OUT | intros Hw; exact (WM _ Hw)]. }
cbn [outside]. split; [| exact I].
destruct CA as [Hsp | [Hcs | (b & Hb & Hr)]]; [lia | |].
- cbn [hl_client_static A4H hla_base] in Hcs. unfold a4_client_static in Hcs. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
+ pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP Hb) as (_ & _ & Hb0 & Hbc & _). lia.
+ apply QSHS.in_fr_ivs in Hb as (Fc & kc & HFc & Hbk).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFc) as (Hkc & HFcal & HFc0 & HFcc & _).
pose proof (QSHS.fr_size_pos kc ltac:(lia)) as FSP.
destruct Hbk as [E | E]; apply pair_equal_spec in E as [-> ->]; [lia|].
unfold shad in Hr. cbn [hl_sb A4L] in Hr. unfold A_SB in Hr. rewrite (QSHS.fr_size_shadow kc) in HFcc by lia.
clear - Hr HFcc HFc0 ACR LO FSP. Z.div_mod_to_equations. lia.
Qed.

Lemma presB_fp : forall A LB LM FRS B mX md Fr S P sp m5 fp,
HEAPAx A LB LM ((Fr, 0) :: FRS) B mX md -> alloc_ceiling <= sp ->
~ client_addr A4H (LB ++ LM) alloc_ceiling fp ->
(forall F' k', In (F', k') ((Fr, 0) :: FRS) -> ~ (F' <= fp < F' + fr_size k') /\ ~ (shad A4L F' <= fp < shad A4L F' + fr_shadow_len k')) ->
(forall a, 0 <= a < 2^64 -> a <> fp -> m5 (wa a) = mX (wa a)) ->
(forall x, wview asegs mX x <> None -> wview asegs m5 x <> None) ->
crls_presB S P (LB ++ LM ++ fr_ivs A4L FRS) sp mX m5.
Proof.
intros A LB LM FRS B mX md Fr S P sp m5 fp HP LSP FPnc FPfr Hoff Hwv a Ha CA NS NP.
split; [| exact (Hwv _)]. apply (Hoff a Ha). intros ->.
destruct CA as [Hsp | [Hcs | (b & Hb & Hr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hcs.
- rewrite app_assoc in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
+ apply FPnc. right; right. exists b. split; [exact Hb | exact Hr].
+ apply QSHS.in_fr_ivs in Hb as (Fc & kc & HFc & Hbk). destruct (FPfr Fc kc (or_intror HFc)) as [N1 N2].
destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP (or_intror HFc)) as (Hkc & _).
destruct Hbk as [E | E]; apply pair_equal_spec in E as [-> ->]; [apply N1; lia | apply N2; lia].
Qed.

Definition crls_B_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(S P ptr rem lo maxlen : Z) (junk data : list byte),
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 maxlen -> 1 <= maxlen <= 20 ->
HEAPAx A LB LM FRS B m md -> Z.of_nat (length FRS) + 1 < 4096 ->

rw_cells asegs m S [CB 24 junk] -> unpoisoned asegs m A_SB S 24 -> S mod 8 = 0 -> arg_locA FRS S 24 ->

rw_cells asegs m P [C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 rem)] -> unpoisoned asegs m A_SB P 16 -> P mod 8 = 0 -> arg_locA FRS P 16 ->
(S + 24 <= P \/ P + 16 <= S) ->

bytes_at asegs m ptr data -> Z.of_nat (length data) = rem -> 0 < ptr -> (rem = 0 \/ exists ab nb, In (ab, nb) LB /\ ab <= ptr /\ ptr + rem <= ab + nb) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - CRLS_STK_B -> bv_unsigned sp mod 32 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
ptr + rem <= lo -> (rem = 0 \/ S + 24 <= ptr \/ ptr + rem <= S) -> (rem = 0 \/ P + 16 <= ptr \/ ptr + rem <= P) ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' (A' : ASA A4L HIx) (n k : Z) (str rest : list byte)
(t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom asegs) ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
crls_presB S P (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' ->
HEAPAx A' LB LM FRS B m' md' -> mem_inv asegs m' ->
0 <= n <= maxlen -> Z.of_nat (length str) <= n -> ~ In (Z_to_bv 8 0) str ->
rw_cells asegs m' S [C1 (Z_to_bv 8 (2 * n)); CB 23 (str ++ Z_to_bv 8 0 :: rest)] ->
0 <= k <= rem -> rw_cells asegs m' P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
bytes_at asegs m' ptr data ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).

Ltac lia' := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ \/ _ |- _ => clear H end; lia.
Ltac if_truex' := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with true; [cbv iota | symmetry; repeat match goal with H : _ \/ _ |- _ => clear H end; solve_condx] end.
Ltac if_falsex' := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
replace c with false; [cbv iota | symmetry; repeat match goal with H : _ \/ _ |- _ => clear H end; solve_condx] end.

Lemma crls_B : crls_B_stmt 0x92528.
Proof.
unfold crls_B_stmt. intros until data. intros A0 A1 A2 Hmax HP FRN OBJ UNS SAL SLOC FDP UNP PAL PLOC SPD SRC LEN PTR0 INB ST LO LOS SPA SHT DLO SDS PDS TP RA K.
subst a0 a1 a2 tp. unfold CRLS_STK_B in LOS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
destruct (heapA_sb_cells A4L HIx _ _ _ _ _ _ _ HP) as (SB1 & SB2 & SB3 & SB4).
apply ro_C8_of_bytes_at in SB1. apply ro_C8_of_bytes_at in SB2. apply ro_C8_of_bytes_at in SB3.
assert (UARC : ro_cells asegs m (hl_uar_cell A4L) [C4 (Z_to_bv 64 1)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SB4]).
clear SB4. a4l.
pose proof (rw_cells_bound _ _ _ _ FDP) as PB. cbn [cells_size csize Nat.add] in PB.
pose proof (rw_cells_bound _ _ _ _ OBJ) as OB. cbn [cells_size csize Nat.add] in OB.
pose proof (bytes_at_bound _ _ _ _ SRC) as DB.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
stash OBJ. stash SRC. stash FDP.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 160%nat ST.
step. stepz. do 13 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -160)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
replace (bv_unsigned sp + -160 - (bv_unsigned sp + -160) mod 32) with (bv_unsigned sp + -160) by (clear - SPA; Z.div_mod_to_equations; lia).
step. step. step. step. step. step. step. step. step. step.
norm_sx32. step. if_false. step. step.
evt_done5.
eapply (stack_malloc_full HIx) with (k := 0) (bytes := 64) (lo := lo) (LB := LB) (LM := LM) (FR := FRS) (B := B);
[ heap_nowA A4L HIx HP MU WM MI | lia | .. ].
all: rewrite ?unsigned_lit by lia.
1: rewrite fr_size_0; lia.
1: reflexivity.
1: lia.
1: exact ST.
1: exact LO.
1: cbn [hl_stack_A A4L]; lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: lia.
1: reflexivity.
1: reflexivity.
intros ms1 m1' md1 A1 Fr RS1 VM1 ST1 HPR1 FRNZ (jff & FF1) SHB1 HP1. open_ret RS1.
rewrite ?unsigned_lit in ST1, HPR1 by lia.
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as (_ & HFal & HF0 & HFc & HFimg & _ & HFshw & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFimg, HFapp. rewrite fr_shadow_len_0 in HFshw. cbn [hl_img_lo hl_img_hi hla_base hl_sb A4L A4H] in HFimg, HFapp.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FR; [| left; cbn; lia].
assert (FSH1 : rw_cells asegs m1' (shad A4L Fr) [CB 8 (repeat (Z_to_bv 8 0) 8)]).
{ split; [split; [cbn; split; [reflexivity | exact I] | cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact SHB1] | exact HFshw]. }
rewrite fr_size_0 in FF1. change (Z.to_nat (64 - 8)) with 56%nat in FF1.
unfold shad in FSH1. a4l.
set (sh := Fr / 8 + 2147450880) in *.
assert (SHR : 2147450880 <= sh /\ sh + 8 <= 17594333495296) by (unfold sh; clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP1) as MI1. change (hl_segs A4L) with asegs in MI1. clear MI.
rename MU into MU0. rename WM into WM0. pose proof (wmono_refl asegs m1') as WM.
pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1') as MU.
unfold A_SB in HFapp.

pose proof SLOC as (Fq & kq & HFq & HSlo & HShi).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 (or_intror HFq)) as (Hkq & HFqal & HFq0 & HFqc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 (or_intror HFq)) as HFqapp. cbn [hl_sb A4L] in HFqapp. unfold A_SB in HFqapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFqapp.
pose proof (QSHS.fr_size_pos kq ltac:(lia)) as FSP.
assert (NEq : Fr <> Fq).
{ intros E. pose proof (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map fr_base fst] in ND.
apply (nodup_cons_notin _ _ _ ND). rewrite E. apply in_map_iff. exists (Fq, kq). split; [reflexivity | exact HFq]. }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF (or_intror HFq) NEq) as APq. rewrite fr_size_0 in APq.
assert (SLO : S + 24 <= lo) by (clear - HShi HFqc LO FSP; lia).
assert (SAPP : S + 24 + 8 <= 2147450880 \/ 17594333495296 <= S) by (clear - HShi HFqapp FSP HSlo; lia).
assert (SFR : Fr + 64 <= S \/ S + 24 <= Fr) by (clear - APq HSlo HShi FSP; lia).
pose proof PLOC as (Fp & kp & HFp & HPlo & HPhi).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP1 (or_intror HFp)) as (Hkp & HFpal & HFp0 & HFpc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP1 (or_intror HFp)) as HFpapp. cbn [hl_sb A4L] in HFpapp. unfold A_SB in HFpapp.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFpapp.
pose proof (QSHS.fr_size_pos kp ltac:(lia)) as FSPp.
assert (NEp : Fr <> Fp).
{ intros E. pose proof (heapA_frame_nodup A4L HIx _ _ _ _ _ _ _ HP1) as ND. cbn [map fr_base fst] in ND.
apply (nodup_cons_notin _ _ _ ND). rewrite E. apply in_map_iff. exists (Fp, kp). split; [reflexivity | exact HFp]. }
pose proof (heapA_frame_apart A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF (or_intror HFp) NEp) as APp. rewrite fr_size_0 in APp.
assert (PLO : P + 16 <= lo) by (clear - HPhi HFpc LO FSPp; lia).
assert (PAPP : P + 16 + 8 <= 2147450880 \/ 17594333495296 <= P) by (clear - HPhi HFpapp FSPp HPlo; lia).
assert (PFR : Fr + 64 <= P \/ P + 16 <= Fr) by (clear - APp HPlo HPhi FSPp; lia).
clear HFqapp HFpapp APq APp HFimg Hkq Hkp HFqal HFpal.

unstash FDP.
apply (rw_cells_transport asegs [(lo, bv_unsigned sp)] _ m1) in FDP; [| exact MU0 | exact WM0 | cbn [disjoint_from]; simpl_sizes; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in FDP.
2:{ eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_frame _ _ _ HFp) | cbn; lia | cbn; lia]. }
change (hl_segs A4H) with asegs in FDP.
assert (UNP1 : unpoisoned asegs m1' A_SB P 16).
{ eapply (QsKa.Mqf.unpoisoned_pres_frame HIx _ _ _ _ _ _ _ LB (bv_unsigned sp + -160) m1 m1' Fp kp P 16 HP HFp HPlo HPhi); [| exact HPR1].
eapply unpoisoned_transport; [exact UNP | exact MU0 |].
intros a k Ha Hk. cbn [disjoint_from]. unfold shadow_span_hi, A_SB in Hk. split; [| exact I]. clear - Ha Hk LO ACR PB PLO. Z.div_mod_to_equations. lia. }
clear UNP.

unstash OBJ.
apply (rw_cells_transport asegs [(lo, bv_unsigned sp)] _ m1) in OBJ; [| exact MU0 | exact WM0 | cbn [disjoint_from]; simpl_sizes; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR1) in OBJ.
2:{ eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply (QSHS.fr_ivs_frame _ _ _ HFq) | cbn; lia | cbn; lia]. }
change (hl_segs A4H) with asegs in OBJ.
assert (UNS1 : unpoisoned asegs m1' A_SB S 24).
{ eapply (QsKa.Mqf.unpoisoned_pres_frame HIx _ _ _ _ _ _ _ LB (bv_unsigned sp + -160) m1 m1' Fq kq S 24 HP HFq HSlo HShi); [| exact HPR1].
eapply unpoisoned_transport; [exact UNS | exact MU0 |].
intros a k Ha Hk. cbn [disjoint_from]. unfold shadow_span_hi, A_SB in Hk. split; [| exact I]. clear - Ha Hk LO ACR OB SLO. Z.div_mod_to_equations. lia. }
clear UNS.
assert (SRC1 : rem <> 0 -> bytes_at asegs m1' ptr data).
{ intros RN. pose proof SRC as X. unstash X.
apply (bytes_at_transport asegs [(lo, bv_unsigned sp)] m m1) in X; [| exact MU0 | cbn [disjoint_from]; rewrite LEN; lia].
destruct INB as [R0 | (ab & nb & Hab & Hlo & Hhi)]; [exfalso; lia|].
eapply (heap_pres_bytes_at A4H); [exact HPR1 | exact X |].
eapply client_range_block; [apply in_or_app; left; exact Hab | lia | cbn; rewrite LEN; lia]. }
clear SRC.
reenterA asegs A4L HIx asegs_wx HP1.
step. step. stepz.
step. if_truex.
stepz.
step. step. step. step.
rewrite (unsigned_lit Fr) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
step. step. step.
stepz. stepz. stepz.
step. step. fold sh.
stepz. stepz. stepz. stepz. step. stepz. stepz. stepz.
stepz. stepz.
stepz. stepz.
step. if_falsex.
step. step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
lazymatch goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
pose proof (crls_fk_HEAPA A1 LB LM FRS B m1' md1 Fr lo (bv_unsigned sp) P S m2 HP1 LO ltac:(lia) SHT PLOC SLOC MU WM MI2) as HP2.
assert (UNS2 : unpoisoned asegs m2 A_SB S 24).
{ eapply unpoisoned_transport; [exact UNS1 | exact MU |].
intros a k Ha Hk. unfold shadow_span_lo, A_SB in Ha. unfold shadow_span_hi, A_SB in Hk. cbn [disjoint_from]. unfold sh.
clear - Ha Hk LO ACR OB SLO SAPP SFR HFal HF0 HFc HFapp PB PLO PAPP HT47 SHT LOS.
repeat split; try exact I; Z.div_mod_to_equations; nia. }
step.
pose proof OBL_AMEMSET_U as AMS. unfold amemset_spec_U, A_MEMSET_U in AMS.
eapply AMS with (d := S) (c := 0) (n := 24) (lo := lo) (old := junk); clear AMS.
1: intros _; exact UNS2.
1: exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HP2).
all: rewrite ?unsigned_lit by lia.
1: lia.
1: lia.
1: left; lia.
1: reflexivity.
1: reflexivity.
1: reflexivity.
1: lia.
1: lia.
1: left; lia.
1: exact OBJ.
1: assumption.
1: exact LO.
1: lia.
1: clear - SPA; Z.div_mod_to_equations; lia.
1: exact MI2.
1: reflexivity.
intros u0' u1' u2' v1' v2' v3' v4' v5' v6' v7' u3' u4' u5' u6' m3 MU3 WM3 MI3 OBJ3 ST3.
transport_after_call asegs m2 m3 MU3 WM3. clear MU3 WM3.
replace (ret_pc (Z_to_bv 64 599628)) with (Z_to_bv 64 599628) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
change (Z.to_nat 24) with 24%nat in OBJ3.

assert (EV : forall mc, munch [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1' mc -> wmono asegs m1' mc -> mem_inv asegs mc ->
HEAPAx A1 LB LM ((Fr, 0) :: FRS) B mc md1 /\ asan_rt_ok mc /\
ro_cells asegs mc (P / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\ ro_cells asegs mc ((P + 8) / 8 + 2147450880) [C1 (Z_to_bv 8 0)] /\
unpoisoned asegs mc A_SB S 24 /\ (0 < rem -> unpoisoned asegs mc A_SB ptr rem)).
{ intros mc MUc WMc MIc.
pose proof (crls_fk_HEAPA A1 LB LM FRS B m1' md1 Fr lo (bv_unsigned sp) P S mc HP1 LO ltac:(lia) SHT PLOC SLOC MUc WMc MIc) as HPc.
split; [exact HPc|]. split; [exact (asan_rt_ok_of_HEAPA HIx _ _ _ _ _ _ _ HPc)|].
assert (UNPc : unpoisoned asegs mc A_SB P 16).
{ eapply unpoisoned_transport; [exact UNP1 | exact MUc |].
intros a k Ha Hk. unfold shadow_span_lo, A_SB in Ha. unfold shadow_span_hi, A_SB in Hk. cbn [disjoint_from]. unfold sh.
clear - Ha Hk LO ACR PB PLO PAPP PFR SPD SAPP OB SLO HFal HF0 HFc HFapp HT47 SHT LOS.
repeat split; try exact I; Z.div_mod_to_equations; nia. }
split; [apply (unpoisoned_al8_ro mc P 16 P UNPc); lia|]. split; [apply (unpoisoned_al8_ro mc P 16 (P + 8) UNPc); [lia | lia | clear - PAL; Z.div_mod_to_equations; lia]|].
split. { eapply unpoisoned_transport; [exact UNS1 | exact MUc |].
intros a k Ha Hk. unfold shadow_span_lo, A_SB in Ha. unfold shadow_span_hi, A_SB in Hk. cbn [disjoint_from]. unfold sh.
clear - Ha Hk LO ACR OB SLO SAPP SFR HFal HF0 HFc HFapp PB PLO PAPP HT47 SHT LOS.
repeat split; try exact I; Z.div_mod_to_equations; nia. }
intros Hr. destruct INB as [R0 | (ab & nb & Hab & Hlo & Hhi)]; [exfalso; lia|].
eapply (unpoisoned_of_blk HIx _ _ _ _ _ _ _ ab nb ptr rem HPc Hab Hlo Hhi Hr). }
assert (SRCF : forall mc, munch [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1' mc -> bytes_at asegs mc ptr data).
{ intros mc MUc. destruct (Z.eq_dec rem 0) as [R0 | RN].
- assert (data = []) as -> by (destruct data; [reflexivity | cbn in LEN; lia]). apply bytes_at_nil. lia.
- destruct INB as [R0 | (ab & nb & Hab & Hlo & Hhi)]; [exfalso; lia|].
assert (Hab2 : In (ab, nb) (LB ++ LM)) by (apply in_or_app; left; exact Hab).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP1 INF Hab2) as DF. rewrite fr_size_0 in DF.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ ab nb HP1 Hab2) as APP. cbn [hl_sb A4L] in APP. unfold A_SB in APP.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in APP.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ab nb HP1 Hab2) as (_ & _ & Hb0 & Hbc & _).
assert (SDS' : S + 24 <= ptr \/ ptr + rem <= S) by (destruct SDS as [?|?]; [lia | assumption]).
assert (PDS' : P + 16 <= ptr \/ ptr + rem <= P) by (destruct PDS as [?|?]; [lia | assumption]).
eapply bytes_at_transport; [exact (SRC1 RN) | exact MUc |]. cbn [disjoint_from]. rewrite LEN. unfold sh.
clear - DF APP Hb0 Hbc SDS' PDS' Hlo Hhi DLO LOS HT47 LO ACR SHR DB LEN PTR0. repeat split; try exact I; lia. }

destruct (EV _ MU WM MI3) as (_ & _ & SHP & SHP8 & _ & _).
step. step. step. sh_norm.
step. rewrite ?zxb_zero. step. if_false.
step. step. step. step.
step.

assert (OBJz : rw_cells asegs m3 S ([C1 b0] ++ ([CB 0 []] ++ ([C1 b0; C1 b0] ++ [CB 21 (repeat b0 21)])))).
{ eapply rw_cells_recast; [exact OBJ3 | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity]. }
clear OBJ3.
apply (proj1 (rw_cells_app asegs m3 S _ _)) in OBJz as [SZ0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. change (Z.of_nat 1) with 1 in OBJz.
apply (proj1 (rw_cells_app asegs m3 _ _ _)) in OBJz as [DATA0 OBJz]. cbn [cells_size csize Nat.add] in OBJz. rewrite Z.add_0_r in OBJz.
apply (proj1 (rw_cells_app asegs m3 _ _ _)) in OBJz as [WIN0 REST0]. cbn [cells_size csize Nat.add] in REST0. change (Z.of_nat 2) with 2 in REST0.
replace (S + 1) with (S + 0 + 1) in WIN0 by lia. replace (S + 1 + 2) with (S + 0 + 3) in REST0 by lia.

assert (J : forall (r : Z) (xa2 : word), 0 <= r <= maxlen ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR (Z_to_bv 64 599700) (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) u0' u1' u2' sp (Z_to_bv 64 (bv_unsigned sp + -160))
(Z_to_bv 64 S) (Z_to_bv 64 r) xa2 v3' v4' v5' v6' v7' (Z_to_bv 64 S) s3 (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 maxlen)
(Z_to_bv 64 2147450880) (Z_to_bv 64 S) s9 (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (Fr + 32)) u3' u4' u5' u6')
F (Z_to_bv 64 599700) fc None m3 (seg_rom asegs))).
2:{ destruct (Z_lt_dec rem maxlen) as [LT | GE].
- if_truex.
step. step. sh_norm. step. rewrite ?zxb_zero. step. if_false.
step. step. step.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply reserve_spec with (S := S) (n := 0) (r := rem) (szb := b0) (rest := @nil cell) | unfold reserve_post; post_call segs mm] end.
all: try reflexivity. 1: lia. 1: exact SZ0. 1: exact MI3.
apply J. lia.
- if_falsex. step.
step. step. sh_norm.
rewrite (div8_add Fr 32) by lia. change (32 / 8) with 4.
replace (Fr / 8 + 4 + 2147450880) with (sh + 4) by (unfold sh; lia).
step. rewrite ?zxb_zero. step. if_false.
step. step. step.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [eapply reserve_spec with (S := S) (n := 0) (r := maxlen) (szb := b0) (rest := @nil cell) | unfold reserve_post; post_call segs mm] end.
all: try reflexivity. 1: lia. 1: exact SZ0. 1: exact MI3.
apply J. lia. }
intros r xa2 Hr.
clear SHP SHP8.
step. step. if_falsex.
step. step. step. step. sh_norm. step.
lazymatch type of FR with rw_cells _ _ _ [_; _; _; _; CB 16 ?j; _; _; _; _; _; _; _; _; _; _; _; _; _; _] => set (fj16 := j) in FR end.
lazymatch type of FF1 with rw_cells _ _ _ [_; _; _; CB 8 ?a; _; CB 16 ?b] => set (hj8 := a) in FF1; set (hj16 := b) in FF1 end.

assert (DONEB : forall (mc : word -> option byte) (n k : Z) (szb j : byte) (s rest : list byte)
(xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
rw_cells asegs mc (bv_unsigned sp + -160)
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 Fr); C8 (Z_to_bv 64 Fr); CB 16 fj16; C8 (Z_to_bv 64 Fr);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 85832); C8 (Z_to_bv 64 599336); CB 8 hj8; C8 (Z_to_bv 64 maxlen); CB 16 hj16] ->
rw_cells asegs mc sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
stk asegs mc lo (bv_unsigned sp + -160) ->
bv_unsigned szb = 2 * n -> 0 <= n <= maxlen ->
rw_cells asegs mc S [C1 szb] ->
rw_cells asegs mc (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs mc (S + n + 1) [C1 b0; C1 j] ->
rw_cells asegs mc (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k <= rem ->
rw_cells asegs mc P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
munch [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1' mc -> wmono asegs m1' mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 (Z_to_bv 64 2147450880) (Z_to_bv 64 S) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x92780) fc None mc (seg_rom asegs))).
{
intros mc n k szb j s rest yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys9 ys10 ys11 yt3 yt4 yt5 yt6
FRc FFc FSHc STc Hsz Hn SZ DATA WIN REST Hk FDPc MUc WMc MIc.
clear FR FF1 FSH1 FDP SZ0 DATA0 WIN0 REST0 MU WM MI3 ST3.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
destruct (EV _ MUc WMc MIc) as (HPc & _ & _ & _ & UNSc & _).
pose proof (unpoisoned_al8_ro mc S 24 S UNSc ltac:(clear; lia) ltac:(clear; lia) SAL) as SH0.
clear HFapp.
rename MUc into MU. rename WMc into WM.
step. step. sh_norm. step. rewrite ?sxb_zero. step. if_false.
step. change (zxb szb) with (Z_to_bv 64 (bv_unsigned szb)). rewrite Hsz.
step. rewrite (unsigned_lit (2 * n)) by lia'. rewrite land1_even.
step. if_false.
step. rewrite (unsigned_lit (2 * n)) by lia'. rewrite shiftr1_double by lia'.
step. rewrite (unsigned_lit n) by lia'.
step.
assert (TAIL : forall xa1 : word,
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
(Z_to_bv 64 (2 * n)) xa1 (Z_to_bv 64 23) ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 (Z_to_bv 64 2147450880) (Z_to_bv 64 S) ys9 ys10 ys11 yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x927b0) fc None mc (seg_rom asegs))).
2:{ destruct (Z_lt_dec n 16) as [Hn16 | Hn16].
- pose proof (lor7_bound n ltac:(lia')) as L7. step. if_truex'. apply TAIL.
- pose proof (lor7_eq23 n ltac:(lia')) as L7. step. rewrite L7. if_falsex'. step. apply TAIL. }
intros xa1.
step. step. step. step. if_falsex'. step. step. if_false. step.

step. step. stepz.
step. step. if_falsex'. step. step. step.
stepz. stepz. stepz. stepz. stepz. stepz. stepz. stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc' _) => lazymatch goal with MUc : munch _ m1' mc', WMc : wmono asegs m1' mc', MIc' : mem_inv asegs mc' |- _ =>
destruct (EV _ MUc WMc MIc') as (HPY & _); rename MUc into MUY; rename WMc into WMY end end.
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPY INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia'.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPY | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia'; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m5 md5 A5 VM5 HP5 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP5. rewrite Z.eqb_refl in HP5.
lazymatch type of HPY with HEAPA _ _ _ _ _ _ _ ?mq _ => rename mq into mX end.
assert (MUr : munch [(fp, fp + 1)] mX m5).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m5) by exact Hwv.
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPS : fp + 1 <= S \/ S + 24 <= fp) by (destruct (FPfr Fq kq (or_intror HFq)) as [N1 _]; lia).
assert (FPP : fp + 1 <= P \/ P + 16 <= fp) by (destruct (FPfr Fp kp (or_intror HFp)) as [N1 _]; lia).
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
pose proof (obj_join asegs mX S n szb j s rest ltac:(lia') Hsz SZ DATA WIN REST) as OBJX. clear SZ DATA WIN REST.
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in OBJX; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FRc; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] _ m5) in FDPc; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] _ m5) in STc; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
assert (SRC5 : bytes_at asegs m5 ptr data).
{ destruct INB as [R0 | (ab & nb & Hab & Hlo & Hhi)].
- assert (data = []) as -> by (destruct data; [reflexivity | cbn in LEN; lia]). apply bytes_at_nil. clear - DB DLO LO ACR LOS SHT HT47. cbn in DB. lia.
- assert (FPD : fp + 1 <= ptr \/ ptr + rem <= fp) by (assert (~ (ab <= fp < ab + nb)) by (intros Hc; apply FPnc; right; right; exists (ab, nb); split; [apply in_or_app; left; exact Hab | cbn; clear - Hc; lia]); clear - H Hlo Hhi; lia).
eapply bytes_at_transport; [exact (SRCF _ MUY) | exact MUr | cbn [disjoint_from]; rewrite LEN; clear - FPD; lia]. }
try clear FFc; try clear FSHc; try clear FPC; try clear SH0.
change (600168 + 4) with 600172.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
do 13 step.
step. step.
evt_done5.

try (replace (bv_unsigned sp + -160 + 160) with (bv_unsigned sp) by (clear; lia)). try rewrite (Z_to_bv_bv_unsigned sp).
destruct (first_nul_split s (j :: rest)) as (str & rest' & Estr & NONUL & Hlen).
rewrite Estr in OBJX.
eapply (K _ m5 md5 A5 n k str rest').
+ reflexivity.
+ eapply model_vm_only_trans; [exact VM1 | exact VM5].
+ release_frame FRc STc (bv_unsigned sp). exact STc.
+ eapply presB_trans; [eapply (presB_stack _ _ _ _ _ _ _ _ _ _ _ _ HP LO MU0 WM0) |].
eapply presB_trans; [eapply (presB_heap_pres _ _ _ _ _ _ _ HPR1); lia |].
eapply presB_trans; [eapply (crls_fk_pres A1 LB LM FRS B m1' md1 Fr lo (bv_unsigned sp) P S mX HP1 LO ltac:(clear - LOS; lia) MUY WMY) |].
eapply (presB_fp A1 LB LM FRS B mX md1 Fr S P (bv_unsigned sp) m5 fp HPY ltac:(clear - LOS LO; lia) FPnc FPfr Hoff Hwv).
+ exact HP5.
+ pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5. exact MI5.
+ clear - Hn; lia.
+ rewrite Ls in Hlen. clear - Hlen Hn; lia.
+ exact NONUL.
+ exact OBJX.
+ clear - Hk; lia.
+ exact FDPc.
+ exact SRC5. }

assert (LOOPB : forall (fuel : nat) (i : Z) (mc : word -> option byte) (n k : Z) (szb j : byte) (s rest : list byte)
(xra xt0 xt1 xt2 xa0 wa1 wa2 xa3 wa4 wa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
maxlen - i <= Z.of_nat fuel -> 0 <= i < maxlen -> 0 <= n <= i ->
rw_cells asegs mc (bv_unsigned sp + -160)
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 Fr); C8 (Z_to_bv 64 Fr); CB 16 fj16; C8 (Z_to_bv 64 Fr);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 85832); C8 (Z_to_bv 64 599336); CB 8 hj8; C8 (Z_to_bv 64 maxlen); CB 16 hj16] ->
rw_cells asegs mc sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
stk asegs mc lo (bv_unsigned sp + -160) ->
bv_unsigned szb = 2 * n ->
rw_cells asegs mc S [C1 szb] ->
rw_cells asegs mc (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs mc (S + n + 1) [C1 b0; C1 j] ->
rw_cells asegs mc (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
0 <= k <= rem ->
rw_cells asegs mc P [C8 (Z_to_bv 64 (ptr + k)); C8 (Z_to_bv 64 (rem - k))] ->
munch [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1' mc -> wmono asegs m1' mc -> mem_inv asegs mc ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) xt0 xt1 xt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
xa0 wa1 wa2 xa3 wa4 wa5 xa6 xa7 (Z_to_bv 64 (-1)) (Z_to_bv 64 92) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 i)
(Z_to_bv 64 2147450880) (Z_to_bv 64 S) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (Fr + 32)) xt3 xt4 xt5 xt6)
F (Z_to_bv 64 0x926b0) fc None mc (seg_rom asegs))).
{ induction fuel as [|fuel IH]; intros i mc n k szb j s rest yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
Hfuel Hi Hn FRc FFc FSHc STc Hsz SZ DATA WIN REST Hk FDPc MUc WMc MIc; [exfalso; lia|].
clear FR FF1 FSH1 FDP SZ0 DATA0 WIN0 REST0 MU WM MI3 ST3.
pose proof (bv_unsigned_in_range 8 szb) as SR. unfold bv_modulus in SR. cbn in SR.
assert (Ls : length s = Z.to_nat n) by (destruct DATA as [[[Hwf _] _] _]; exact Hwf).
assert (Lr : length rest = Z.to_nat (21 - n)) by (destruct REST as [[[Hwf _] _] _]; exact Hwf).
rename MUc into MU. rename WMc into WM.
destruct (EV _ MU WM MIc) as (HPc & _ & SHP & SHP8 & UNSc & UNDc).
pose proof (SRCF _ MU) as SRCc.
clear HFapp INB.

assert (PUSHK : forall (k' : Z) (mc' : word -> option byte) (c : byte) (za0 za2 za3 za4 za5 za6 za7 : word),
k < k' <= rem ->
rw_cells asegs mc' (bv_unsigned sp + -160)
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 sh); C8 (Z_to_bv 64 Fr); C8 (Z_to_bv 64 Fr); CB 16 fj16; C8 (Z_to_bv 64 Fr);
C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
rw_cells asegs mc' Fr [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 85832); C8 (Z_to_bv 64 599336); CB 8 hj8; C8 (Z_to_bv 64 maxlen); CB 16 hj16] ->
rw_cells asegs mc' sh [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)] ->
stk asegs mc' lo (bv_unsigned sp + -160) ->
rw_cells asegs mc' S [C1 szb] -> rw_cells asegs mc' (S + 1) [CB (Z.to_nat n) s] ->
rw_cells asegs mc' (S + n + 1) [C1 b0; C1 j] -> rw_cells asegs mc' (S + n + 3) [CB (Z.to_nat (21 - n)) rest] ->
rw_cells asegs mc' P [C8 (Z_to_bv 64 (ptr + k')); C8 (Z_to_bv 64 (rem - k'))] ->
munch [(lo, bv_unsigned sp); (P, P + 16); (S, S + 24); (Fr, Fr + 56); (sh, sh + 8)] m1' mc' -> wmono asegs m1' mc' -> mem_inv asegs mc' ->
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
za0 (Z_to_bv 64 (bv_unsigned c)) za2 za3 za4 za5 za6 za7 (Z_to_bv 64 (-1)) (Z_to_bv 64 92) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 i)
(Z_to_bv 64 2147450880) (Z_to_bv 64 S) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (Fr + 32)) yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x9274c) fc None mc' (seg_rom asegs))).
{ intros k' mc' c za0 za2 za3 za4 za5 za6 za7 Hk' FRd FFd FSHd STd SZd DATAd WINd RESTd FDPd MUd WMd MId.
clear FRc FFc FSHc STc SZ DATA WIN REST FDPc MU WM MIc SRCc SHP SHP8 UNSc UNDc HPc.
rename MUd into MU. rename WMd into WM.
pose proof (bv_unsigned_in_range 8 c) as CR. unfold bv_modulus in CR. cbn in CR.
step. step.
call_pushb S n lo szb b0 j.
all: lazymatch goal with
| |- evt _ _ _ => idtac
| |- Z_to_bv _ _ = Z_to_bv _ _ => reflexivity
| |- bv_unsigned _ = 2 * _ => assumption
| |- rw_cells _ _ _ [C1 _] => assumption
| |- rw_cells _ _ _ [C1 _; C1 _] => assumption
| |- stk _ _ _ _ => assumption
| |- mem_inv _ _ => assumption
| |- _ => rewrite ?unsigned_lit by lia'; lia
end.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m7 end.
lazymatch goal with H : rw_cells asegs m7 S [C1 ?sz] |- _ => rename H into SZ7 end.
lazymatch goal with H : rw_cells asegs m7 (S + n + 1) _ |- _ => rename H into WIN7 end.
lazymatch goal with H : rw_cells asegs m7 (S + 1) _ |- _ => rename H into DATA7 end.
lazymatch goal with H : rw_cells asegs m7 (S + n + 3) _ |- _ => rename H into REST7 end.
lazymatch goal with H : rw_cells asegs m7 P _ |- _ => rename H into FDP7 end.
lazymatch goal with H : rw_cells asegs m7 (bv_unsigned sp + -160) _ |- _ => rename H into FR7 end.
lazymatch goal with H : rw_cells asegs m7 Fr _ |- _ => rename H into FF7 end.
lazymatch goal with H : rw_cells asegs m7 sh _ |- _ => rename H into FSH7 end.
lazymatch goal with H : stk asegs m7 lo _ |- _ => rename H into ST7 end.
lazymatch goal with H : munch _ m1' m7 |- _ => rename H into MU7 end.
lazymatch goal with H : wmono asegs m1' m7 |- _ => rename H into WM7 end.
lazymatch goal with H : mem_inv asegs m7 |- _ => rename H into MI7 end.
lazymatch goal with H : bv_unsigned ?szb' = 2 * (n + 1) |- _ => rename H into Hsz7 end.
destruct (rw_cells_unpair _ _ _ _ _ WIN7) as [Hcb Hnul]. clear WIN7.
replace (S + n + 1) with (S + 1 + Z.of_nat (Z.to_nat n)) in Hcb by lia'.
pose proof (rw_cells_CB_snoc _ _ _ _ _ _ DATA7 Hcb) as DATA3. clear DATA7 Hcb.
replace (Datatypes.S (Z.to_nat n)) with (Z.to_nat (n + 1)) in DATA3 by lia'.
destruct rest as [|j' rest']; [cbn in Lr; exfalso; lia|].
replace (Z.to_nat (21 - n)) with (Datatypes.S (Z.to_nat (21 - (n + 1)))) in REST7 by lia'.
destruct (rw_cells_CB_head _ _ _ _ _ _ REST7) as [Hj' REST3]. clear REST7.
replace (S + n + 1 + 1) with (S + (n + 1) + 1) in Hnul by lia'.
replace (S + n + 3) with (S + (n + 1) + 1 + 1) in Hj' by lia'.
pose proof (rw_cells_pair _ _ _ _ _ Hnul Hj') as WIN3. clear Hnul Hj'.
replace (S + n + 3 + 1) with (S + (n + 1) + 3) in REST3 by lia'.

step. step. step.
destruct (Z_lt_dec (i + 1) maxlen) as [CONT | LAST].
- if_truex'.
eapply (IH (i + 1) m7 (n + 1) k') ;
[ lia' | lia' | lia' | exact FR7 | exact FF7 | exact FSH7 | exact ST7 | exact Hsz7 | exact SZ7 | exact DATA3 | exact WIN3 | exact REST3 | lia' | exact FDP7 | exact MU7 | exact WM7 | exact MI7 ].
- if_falsex'. step.
eapply (DONEB m7 (n + 1) k');
[ exact FR7 | exact FF7 | exact FSH7 | exact ST7 | exact Hsz7 | lia' | exact SZ7 | exact DATA3 | exact WIN3 | exact REST3 | lia' | exact FDP7 | exact MU7 | exact WM7 | exact MI7 ]. }

step. rewrite ?zxb_zero. step. if_false.
step. step.
destruct (Z.eq_dec (rem - k) 0) as [RK0 | RKN].
{ if_truex'.
eapply (DONEB mc n k); [exact FRc | exact FFc | exact FSHc | exact STc | exact Hsz | lia' | exact SZ | exact DATA | exact WIN | exact REST | lia' | exact FDPc | exact MU | exact WM | exact MIc]. }
if_falsex'.

step. rewrite ?zxb_zero. step. if_false.
step.
step. if_falsex'.
step. rewrite (neq_wz (ptr + k) (-1)) by (clear - DB DLO Hk LO ACR LOS SHT HT47 LEN; lia). cbv beta iota.
destruct (unpoisoned_byte_ro mc ptr rem (ptr + k) (UNDc ltac:(lia')) ltac:(lia')) as (sv1 & SHK & Hsv1).
destruct (nth_error data (Z.to_nat k)) as [b1|] eqn:Hb1; [| exfalso; apply nth_error_None in Hb1; lia].
pose proof (bv_unsigned_in_range 8 b1) as B1R. unfold bv_modulus in B1R. cbn in B1R.
step. step. sh_norm. step. step.
assert (B88 : forall (wa1 wa2 : word),
evt asegs (AJ5e A4L HIx A1 T md1)
(MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
(Z_to_bv 64 (ptr + k)) wa1 wa2 (Z_to_bv 64 (rem - k)) ya4 ya5 ya6 ya7 (Z_to_bv 64 (-1)) (Z_to_bv 64 92) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 i)
(Z_to_bv 64 2147450880) (Z_to_bv 64 S) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (Fr + 32)) yt3 yt4 yt5 yt6)
F (Z_to_bv 64 0x926e4) fc None mc (seg_rom asegs))).
2:{ destruct Hsv1 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply B88.
- rewrite (QsKa.Mqa.sxb_small sv1) by lia'. if_truex'. step. step.
rewrite (unsigned_lit (ptr + k)) by lia'. rewrite QsKa.Mqa.land7_mod8 by lia'. if_falsex'. step. apply B88. }
intros wa1 wa2. clear SHK sv1 Hsv1.
step. rewrite ?zxb_zero. step. if_false.
pose proof (u8ro_read asegs mc ptr data k b1 _ SRCc Hb1 ltac:(lia') eq_refl) as RD1.
step. clear RD1. change (zxb b1) with (Z_to_bv 64 (bv_unsigned b1)).
step.
clear SHP SHP8.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => lazymatch goal with MUq : munch _ m1' mq, WMq : wmono asegs m1' mq, MIq : mem_inv asegs mq |- _ =>
destruct (EV _ MUq WMq MIq) as (_ & _ & _ & SHP8b & _ & _) end end.
step. rewrite ?zxb_zero. step. if_false. clear SHP8b.
step. step.
step.
destruct (Z.eq_dec (bv_unsigned b1) 92) as [E92 | N92].
2:{
if_truex'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MUx : munch _ m1' mx, WMx : wmono asegs m1' mx, MIx : mem_inv asegs mx |- _ =>
eapply (PUSHK (k + 1) mx b1); [lia' | exact FRc | exact FFc | exact FSHc | exact STc | exact SZ | exact DATA | exact WIN | exact REST | | exact MUx | exact WMx | exact MIx] end end.
replace (rem - (k + 1)) with (rem - k + -1) by lia'. replace (ptr + (k + 1)) with (ptr + k + 1) by lia'. exact FDPc. }
if_falsex'.
step.
destruct (Z.eq_dec (rem - k - 1) 0) as [R0 | R1].
{
if_truex'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MUx : munch _ m1' mx, WMx : wmono asegs m1' mx, MIx : mem_inv asegs mx |- _ =>
eapply (PUSHK (k + 1) mx b1); [lia' | exact FRc | exact FFc | exact FSHc | exact STc | exact SZ | exact DATA | exact WIN | exact REST | | exact MUx | exact WMx | exact MIx] end end.
replace (rem - (k + 1)) with (rem - k + -1) by lia'. replace (ptr + (k + 1)) with (ptr + k + 1) by lia'. exact FDPc. }
if_falsex'.

step. rewrite (neq_wz (ptr + k + 1) (-1)) by (clear - DB DLO Hk LO ACR LOS SHT HT47 LEN R1; lia). cbv beta iota.
destruct (nth_error data (Z.to_nat (k + 1))) as [b2|] eqn:Hb2; [| exfalso; apply nth_error_None in Hb2; lia].
pose proof (bv_unsigned_in_range 8 b2) as B2R. unfold bv_modulus in B2R. cbn in B2R.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => lazymatch goal with MUq : munch _ m1' mq, WMq : wmono asegs m1' mq, MIq : mem_inv asegs mq |- _ =>
destruct (EV _ MUq WMq MIq) as (_ & _ & SHPc & _ & _ & UNDd); pose proof (SRCF _ MUq) as SRCd;
destruct (unpoisoned_byte_ro mq ptr rem (ptr + k + 1) (UNDd ltac:(lia')) ltac:(lia')) as (sv2 & SHK2 & Hsv2) end end.
step. step. sh_norm. step. step.
lazymatch goal with |- evt _ ?Q (MS _ ?FF _ ?fcc _ ?mm _) =>
assert (BBC : forall (wa4 wa5 : word),
evt asegs Q (MS (mkR yra (Z_to_bv 64 (bv_unsigned sp + -160)) gp (Z_to_bv 64 6444320) yt0 yt1 yt2 sp (Z_to_bv 64 (bv_unsigned sp + -160))
(Z_to_bv 64 (ptr + k)) (Z_to_bv 64 (bv_unsigned b1)) (Z_to_bv 64 (ptr + k + 1)) (Z_to_bv 64 (rem - k)) wa4 wa5 ya6 ya7
(Z_to_bv 64 (-1)) (Z_to_bv 64 92) (Z_to_bv 64 P) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 i)
(Z_to_bv 64 2147450880) (Z_to_bv 64 S) (Z_to_bv 64 (P / 8 + 2147450880)) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) (Z_to_bv 64 (Fr + 32)) yt3 yt4 yt5 yt6)
FF (Z_to_bv 64 0x92724) fcc None mm (seg_rom asegs))) end.
2:{ destruct Hsv2 as [-> | [Hv8 Hvm]].
- rewrite sxb_zero. if_false. apply BBC.
- rewrite (QsKa.Mqa.sxb_small sv2) by lia'. if_truex'. step. step.
rewrite (unsigned_lit (ptr + k + 1)) by lia'. rewrite QsKa.Mqa.land7_mod8 by lia'. if_truex'. apply BBC. }
intros wa4 wa5. clear SHK2 sv2 Hsv2.
step. rewrite ?zxb_zero. step. if_false.
pose proof (u8ro_read asegs _ ptr data (k + 1) b2 _ SRCd Hb2 ltac:(lia') eq_refl) as RD2.
replace (ptr + (k + 1)) with (ptr + k + 1) in RD2 by lia'.
step. clear RD2. change (zxb b2) with (Z_to_bv 64 (bv_unsigned b2)).
step.
clear SHPc UNDd SRCd.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => lazymatch goal with MUq : munch _ m1' mq, WMq : wmono asegs m1' mq, MIq : mem_inv asegs mq |- _ =>
destruct (EV _ MUq WMq MIq) as (_ & _ & _ & SHP8c & _ & _) end end.
step. rewrite ?zxb_zero. step. if_false. clear SHP8c.
step. step.
step.
destruct (Z.eq_dec (bv_unsigned b2) 92) as [F92 | M92].
-
if_falsex'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MUx : munch _ m1' mx, WMx : wmono asegs m1' mx, MIx : mem_inv asegs mx |- _ =>
eapply (PUSHK (k + 2) mx b1); [lia' | exact FRc | exact FFc | exact FSHc | exact STc | exact SZ | exact DATA | exact WIN | exact REST | | exact MUx | exact WMx | exact MIx] end end.
replace (rem - (k + 2)) with (rem - k + -2) by lia'. replace (ptr + (k + 2)) with (ptr + k + 2) by lia'. exact FDPc.
-
if_truex'.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => lazymatch goal with MUx : munch _ m1' mx, WMx : wmono asegs m1' mx, MIx : mem_inv asegs mx |- _ =>
eapply (DONEB mx n (k + 2)); [exact FRc | exact FFc | exact FSHc | exact STc | exact Hsz | lia' | exact SZ | exact DATA | exact WIN | exact REST | lia' | | exact MUx | exact WMx | exact MIx] end end.
replace (ptr + (k + 2)) with (ptr + k + 2) by lia'. replace (rem - (k + 2)) with (rem - k + -2) by lia'. exact FDPc. }

replace (Z_to_bv 64 ptr) with (Z_to_bv 64 (ptr + 0)) in FDP by (rewrite Z.add_0_r; reflexivity).
replace (Z_to_bv 64 rem) with (Z_to_bv 64 (rem - 0)) in FDP by (rewrite Z.sub_0_r; reflexivity).
eapply (LOOPB (Z.to_nat maxlen) 0 m3 0 0 b0 b0 (@nil byte) (repeat b0 21));
[ lia' | lia' | lia' | exact FR | exact FF1 | exact FSH1 | exact ST3 | reflexivity | exact SZ0 | exact DATA0 | exact WIN0 | exact REST0 | lia' | exact FDP | exact MU | exact WM | exact MI3 ].
Qed.
End ACrls.

Theorem crls_A : forall HIx, crls_B_stmt HIx 0x92528.
Proof. intros HIx. exact (crls_B HIx QpNt.Mq8.amemset_U). Qed.
End RC__1.
