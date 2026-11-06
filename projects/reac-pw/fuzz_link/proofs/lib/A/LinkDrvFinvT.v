From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.reac_pw.fuzz_link.images Require Import Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK00 YK0s YK15 YK18 YP0m YP09 YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YCbq YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD1y AD1u AD1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* FINV (AD1u.v) at a general kept list T across one allocator call of the driver's tail: the kept block of T
   is a live block of the ledger, so it is disjoint from the block the call frees, it is unowned before and
   after, and it is neither stack scratch nor errno. *)

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma pairwise_any : forall {X : Type} (R : X -> X -> Prop) (l : list X) (x y : X),
pairwise R l -> In x l -> In y l -> x = y \/ R x y \/ R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x y P Hx Hy; [destruct Hx|].
cbn [pairwise] in P. destruct P as [F P].
destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
- left. rewrite <- Hx, <- Hy. reflexivity.
- right. left. rewrite <- Hx. exact (proj1 (Forall_forall _ _) F y Hy).
- right. right. rewrite <- Hy. exact (proj1 (Forall_forall _ _) F x Hx).
- exact (IH x y P Hx Hy).
Qed.

(* amf_gi (AMemFileSink.v) leaves exactly two shapes for the kept list. *)
Lemma finv_T_shape : forall (T : list (Z * Z)) (H : word -> bool) (m : word -> option byte),
FINV T H m -> T = [] \/ exists f, T = [(f, AMF_BLOCK)].
Proof.
intros T H m (HG & _ & _ & _).
destruct HG as [(_ & HT) | (f & _ & HT & _)]; [left; exact HT | right; exists f; exact HT].
Qed.

Lemma finv_T_size : forall (T : list (Z * Z)) (H : word -> bool) (m : word -> option byte) q n,
FINV T H m -> In (q, n) T -> n = AMF_BLOCK.
Proof.
intros T H m q n HFI Hin. destruct (finv_T_shape T H m HFI) as [HT | (f & HT)]; rewrite HT in Hin.
- destruct Hin.
- cbn [In] in Hin. destruct Hin as [Heq | []]. injection Heq as E1 E2. exact (eq_sym E2).
Qed.

(* two live blocks of different size are apart (the block law's pairwise disjointness) *)
Lemma blocks_apart : forall (B : asyms) (ARL : AR_laws tfibsegs B) ly S W mem md p n q m a,
AR tfibsegs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (q, m) (ablocks B ly S) ->
req_size n <> req_size m -> p <= a < p + req_size n -> q <= a < q + req_size m -> False.
Proof.
intros B ARL ly S W mem md p n q m a HAR Hp Hq Hne Hpa Hqa.
pose proof (al_sep _ _ ARL ly S W mem md HAR) as [PD _].
destruct (pairwise_any zdisjoint _ (p, req_size n) (q, req_size m) PD
  (in_or_app _ _ _ (or_introl (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (p, n) Hp)))
  (in_or_app _ _ _ (or_introl (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (q, m) Hq))))
  as [Heq | [D | D]].
- injection Heq as E1 E2. exact (Hne E2).
- unfold zdisjoint in D. cbn [fst snd] in D. lia.
- unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* free keeps every block of the ledger but the one it frees, and the layout keeps the addresses *)
Lemma incl_free_keep : forall (B : asyms) (ARL : AR_laws tfibsegs B)
  ly S W mem md ly' S' (pb : sptr) (cap : Z) (T : list (Z * Z)) l1 l2 (H : word -> bool) (m : word -> option byte),
AR tfibsegs B ly S W mem md -> layout_le (length (st_secs S)) ly ly' ->
((pb = PNull /\ l1 ++ l2 = blocks S) \/ blocks S = l1 ++ (pb, cap) :: l2) -> blocks S' = l1 ++ l2 ->
FINV T H m -> 65536 <= cap ->
incl T (ablocks B ly S) -> incl T (ablocks B ly' S').
Proof.
intros B ARL ly S W mem md ly' S' pb cap T l1 l2 H m HAR Hle Hsp Hbl HFI Hcap Hinc.
assert (RB : AMF_BLOCK = 1304) by reflexivity.
pose proof (al_layout _ _ ARL ly S W mem md ly' HAR Hle) as (HAB & _ & _).
intros x Hx. destruct x as [q n].
pose proof (finv_T_size T H m q n HFI Hx) as Hn.
pose proof (Hinc _ Hx) as Hin. rewrite <- HAB in Hin.
unfold ablocks in Hin. unfold ablocks. rewrite Hbl.
apply in_map_iff in Hin. destruct Hin as (b & Hb & Hbin).
apply in_map_iff. exists b. split; [exact Hb|].
destruct Hsp as [(_ & Heq) | Heq].
- rewrite <- Heq in Hbin. exact Hbin.
- rewrite Heq in Hbin. apply in_app_or in Hbin. apply in_or_app.
  destruct Hbin as [H1 | H1]; [left; exact H1 | right].
  cbn [In] in H1. destruct H1 as [H1 | H1]; [| exact H1].
  exfalso. rewrite <- H1 in Hb. cbn [fst snd] in Hb. injection Hb as E1 E2. lia.
Qed.

(* no byte of a kept block is a byte of a block of at least 65536 bytes: the two are different live blocks.
   LinkLoopKept.v finv_site_kept carries FINV T over the call itself. *)
Lemma kept_off_block : forall (B : asyms) (ARL : AR_laws tfibsegs B) ly S W mem md (p0 n0 : Z) (T : list (Z * Z)),
AR tfibsegs B ly S W mem md -> In (p0, n0) (ablocks B ly S) -> 65536 <= n0 -> incl T (ablocks B ly S) ->
forall a, in_kept T a -> ~ (p0 <= a < p0 + req_size n0).
Proof.
intros B ARL ly S W mem md p0 n0 T HAR Hin0 Hcap Hinc a Hk Hx. destruct Hk as (f & Hf & Hfa).
assert (RB : AMF_BLOCK = 1304) by reflexivity.
assert (RQB : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity.
assert (RQ0 : req_size n0 = n0) by (unfold req_size; destruct (Z.eqb_spec n0 0); [lia | reflexivity]).
exact (blocks_apart B ARL ly S W mem md f AMF_BLOCK p0 n0 a HAR (Hinc _ Hf) Hin0 ltac:(lia) ltac:(lia) Hx).
Qed.

End b.
