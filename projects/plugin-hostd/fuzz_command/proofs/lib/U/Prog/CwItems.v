From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP ZBridge Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import CommandModel CommandFP CommandTac
  printf_facts_c atoi_c snprintf_c strcmp_c strspn_c strcspn_c check_words_c check_words_chain syntax_reply_matches.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecFacts.
Import ListNotations.
Open Scope Z_scope.

(* The item loop of check_words (0x14cd4 to 0x14e34): it walks the template row of the call's verb, one
   space-separated item per argument, and compares each argument with the item's expected string. *)

Definition SP1 : list byte := [Z_to_bv 8 32].
Definition LIT_SP : Z := 0x1034c.
Definition LIT_EMPTY : Z := 0x1045f.
Definition LIT_PCTD : Z := 0x10828.
Definition CW_TBL : Z := 0x228d0.

(* The item the code reads at [s] (the template after the skipped spaces): its first byte picks the kind. *)
Definition item_of (s : list byte) : witem :=
  let b := bv_unsigned (hd NUL s) in
  if b =? 35 then INum (atoi_val (tl s))
  else if b =? 42 then IStar
  else if b =? 76 then ILine
  else if b =? 63 then IOpt (atoi_val (tl s))
  else IWord (atoi_val s).

Fixpoint tpl_items (f : nat) (s : list byte) : list witem :=
  match f, s with
  | O, _ => []
  | _, [] => []
  | S f', _ :: _ =>
      let s1 := skipn (spn_len SP1 s) s in
      item_of s1 :: tpl_items f' (skipn (cspn_len SP1 s1) s1)
  end.

Definition item_ok (i : witem) : Prop :=
  match i with IWord k | INum k | IOpt k => 0 <= k | _ => True end.

(* A non-null pointer at [A] to the C string [s], both outside the footprint [FW]. *)
Definition ptr_at (m : word -> option byte) (FW : list (Z * Z)) (A : Z) (s : list byte) : Prop :=
  exists p : word, bytes_at rsegs m A (le8 p) /\ disjoint_from FW A 8 /\ bv_unsigned p <> 0 /\
    bytes_at rsegs m (bv_unsigned p) (s ++ [NUL]) /\ disjoint_from FW (bv_unsigned p) (Z.of_nat (length s) + 1).

(* g_call_words (in .data.rel.ro at CW_TBL): the row of verb [fn] is the string at cw_tp fn. *)
Definition cw_tp (fn : Z) : Z :=
  match fn with
  | 0 => 67751 | 1 => 68110 | 2 => 66737 | 3 => 66655 | 4 => 67946 | 5 => 67190 | 6 => 66394 | 7 => 67139
  | 8 => 66655 | 9 => 66737 | 10 => 67344 | 11 => 67491 | 12 => 67717 | 13 => 67491 | 14 => 67143 | 15 => 67717
  | 16 => 67170 | 17 => 67563 | 18 => 66737 | 19 => 68019 | 20 => 66982 | 21 => 67491 | 22 => 67491 | 23 => 67491
  | 24 => 67491 | _ => 67698
  end.

Definition cw_tpl (fn : Z) : list byte :=
  str match fn with
  | 0 => [49; 32; 35; 50; 32; 42; 32; 42] | 1 => [35; 49; 32; 76] | 2 => [35; 49] | 3 => []
  | 4 => [48; 32; 76; 32; 49; 32; 50] | 5 => [76] | 6 => [76; 32; 42; 32; 42] | 7 => [76; 32; 42] | 8 => []
  | 9 => [35; 49] | 10 => [63; 49] | 11 => [49] | 12 => [49; 32; 50] | 13 => [49] | 14 => [49; 32; 35; 50]
  | 15 => [49; 32; 50] | 16 => [49; 32; 50; 32; 51] | 17 => [35; 49; 32; 42; 32; 42] | 18 => [35; 49]
  | 19 => [35; 49; 32; 48] | 20 => [49; 32; 50; 32; 51; 32; 42] | 21 => [49] | 22 => [49] | 23 => [49]
  | 24 => [49] | _ => [42]
  end.

Definition cw_slack (fn : Z) : list byte :=
  match image_bytes rsegs (cw_tp fn + Z.of_nat (length (cw_tpl fn)) + 1) 7 with
  | Some l => l
  | None => []
  end.

Lemma fn_cases : forall fn, 0 <= fn < 26 ->
  fn = 0 \/ fn = 1 \/ fn = 2 \/ fn = 3 \/ fn = 4 \/ fn = 5 \/ fn = 6 \/ fn = 7 \/ fn = 8 \/ fn = 9 \/ fn = 10 \/
  fn = 11 \/ fn = 12 \/ fn = 13 \/ fn = 14 \/ fn = 15 \/ fn = 16 \/ fn = 17 \/ fn = 18 \/ fn = 19 \/ fn = 20 \/
  fn = 21 \/ fn = 22 \/ fn = 23 \/ fn = 24 \/ fn = 25.
Proof. intros fn H. lia. Qed.

Ltac fn_split H := repeat (destruct H as [H|H]; [subst; vm_compute; reflexivity|]); subst; vm_compute; reflexivity.

(* The code's parse of each row is the model's item list. *)
Lemma cw_tpl_items : forall fn, 0 <= fn < 26 -> tpl_items (S (length (cw_tpl fn))) (cw_tpl fn) = call_items fn.
Proof. intros fn H. apply fn_cases in H. fn_split H. Qed.

Ltac fn_split_bv H :=
  repeat (destruct H as [H|H]; [subst; vm_compute; repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ] |]);
  subst; vm_compute; repeat first [ reflexivity | apply bv_eq; reflexivity | f_equal ].

(* The table entry of verb [fn], as the image holds it. *)
Lemma cw_tbl_img : forall fn, 0 <= fn < 26 -> image_bytes rsegs (CW_TBL + 8 * fn) 8 = Some (le8 (Z_to_bv 64 (cw_tp fn))).
Proof. intros fn H. apply fn_cases in H. fn_split_bv H. Qed.

Lemma cw_tpl_ro : forall fn, 0 <= fn < 26 ->
  ro_bytes_b rsegs (cw_tp fn) (cw_tpl fn ++ NUL :: cw_slack fn) = true.
Proof. intros fn H. apply fn_cases in H. fn_split H. Qed.

Lemma cw_tpl_facts : forall fn, 0 <= fn < 26 ->
  forallb (fun z => negb (z =? 0)) (map bv_unsigned (cw_tpl fn)) = true /\
  ((- (cw_tp fn + Z.of_nat (length (cw_tpl fn)) + 1)) mod 8 <=? Z.of_nat (length (cw_slack fn))) = true /\
  ((0x10000 <=? cw_tp fn) && (cw_tp fn + Z.of_nat (length (cw_tpl fn)) + 1 + Z.of_nat (length (cw_slack fn)) <=? 0x12a74)) = true /\
  forallb (fun i => match i with IWord k | INum k | IOpt k => 0 <=? k | _ => true end) (call_items fn) = true.
Proof. intros fn H. apply fn_cases in H. repeat (destruct H as [H|H]; [subst; vm_compute; repeat split|]); subst; vm_compute; repeat split. Qed.


Lemma in_set_sp : forall x, in_set SP1 x = (bv_unsigned x =? 32).
Proof.
  intros x. unfold in_set, SP1. cbn [existsb]. rewrite orb_false_r.
  replace (bv_unsigned (Z_to_bv 8 32)) with 32 by reflexivity. apply Z.eqb_sym.
Qed.

Lemma spn_le : forall s, (spn_len SP1 s <= length s)%nat.
Proof. induction s as [|x s IH]; cbn [spn_len length]; [lia|]. destruct (in_set SP1 x); lia. Qed.

Lemma cspn_le : forall s, (cspn_len SP1 s <= length s)%nat.
Proof. induction s as [|x s IH]; cbn [cspn_len length]; [lia|]. destruct (existsb _ _); lia. Qed.

Lemma spn_stop : forall s, bv_unsigned (hd NUL (skipn (spn_len SP1 s) s)) <> 32.
Proof.
  induction s as [|x s IH].
  - cbn [spn_len skipn hd]. intros E. vm_compute in E. discriminate E.
  - cbn [spn_len]. rewrite in_set_sp.
    destruct (Z.eqb_spec (bv_unsigned x) 32) as [E|E]; cbn [skipn hd]; [exact IH | exact E].
Qed.

Lemma cspn_pos : forall s, bv_unsigned (hd NUL s) <> 32 -> s <> [] -> (1 <= cspn_len SP1 s)%nat.
Proof.
  intros [|x s] H N; [congruence|]. cbn [cspn_len hd] in *. unfold SP1. cbn [existsb].
  replace (bv_unsigned (Z_to_bv 8 32)) with 32 by reflexivity.
  rewrite (proj2 (Z.eqb_neq 32 (bv_unsigned x))) by lia. cbn [orb]. lia.
Qed.

Lemma tpl_items_cons : forall f s, s <> [] ->
  tpl_items (S f) s = item_of (skipn (spn_len SP1 s) s) ::
    tpl_items f (skipn (cspn_len SP1 (skipn (spn_len SP1 s) s)) (skipn (spn_len SP1 s) s)).
Proof. intros f [|x s] H; [congruence|]. reflexivity. Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small.
  replace (bv_half_modulus 64) with (2^63) by reflexivity. lia.
Qed.
Lemma sx32_lit : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_id by lia. reflexivity. Qed.

Lemma tl_skipn : forall (l : list byte) k, tl (skipn k l) = skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k]; cbn; [reflexivity | reflexivity | reflexivity | apply IH]. Qed.

Definition kind_item (bb v : Z) : witem := if bb =? 35 then INum v else if bb =? 63 then IOpt v else IWord v.

Lemma sx32_any : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

Lemma item_of_num : forall s, bv_unsigned (hd NUL s) = 35 ->
  item_of s = kind_item (bv_unsigned (hd NUL s)) (atoi_val (tl s)).
Proof. intros s H. unfold item_of, kind_item. rewrite H. reflexivity. Qed.

Lemma item_of_opt : forall s, bv_unsigned (hd NUL s) = 63 ->
  item_of s = kind_item (bv_unsigned (hd NUL s)) (atoi_val (tl s)).
Proof. intros s H. unfold item_of, kind_item. rewrite H. reflexivity. Qed.

Lemma item_of_star : forall s, bv_unsigned (hd NUL s) = 42 -> item_of s = IStar.
Proof. intros s H. unfold item_of. rewrite H. reflexivity. Qed.

Lemma item_of_line : forall s, bv_unsigned (hd NUL s) = 76 -> item_of s = ILine.
Proof. intros s H. unfold item_of. rewrite H. reflexivity. Qed.

Lemma item_of_word : forall s, bv_unsigned (hd NUL s) <> 35 -> bv_unsigned (hd NUL s) <> 42 ->
  bv_unsigned (hd NUL s) <> 76 -> bv_unsigned (hd NUL s) <> 63 ->
  item_of s = kind_item (bv_unsigned (hd NUL s)) (atoi_val s).
Proof.
  intros s H1 H2 H3 H4. unfold item_of, kind_item.
  rewrite (proj2 (Z.eqb_neq _ 35) H1), (proj2 (Z.eqb_neq _ 42) H2), (proj2 (Z.eqb_neq _ 76) H3),
    (proj2 (Z.eqb_neq _ 63) H4). reflexivity.
Qed.

Lemma adv_ge1 : forall l, l <> [] -> (1 <= spn_len SP1 l + cspn_len SP1 (skipn (spn_len SP1 l) l))%nat.
Proof.
  intros [|x l] H; [congruence|]. cbn [spn_len]. rewrite in_set_sp.
  destruct (Z.eqb_spec (bv_unsigned x) 32) as [E|E]; cbv beta iota; [lia|].
  cbn [skipn cspn_len]. unfold SP1. cbn [existsb]. replace (bv_unsigned (Z_to_bv 8 32)) with 32 by reflexivity.
  rewrite (proj2 (Z.eqb_neq 32 (bv_unsigned x))) by lia. cbn [orb]. lia.
Qed.

Ltac zc H := zify_cond H; rewrite ?unsigned_lit in H by lia; rewrite ?Z.mod_small in H by lia.

Section CW.
Variables (gp tp s4 s9 : word) (F : bvmap 5 word) (m0 : word -> option byte)
  (lo S T AP nargs r : Z) (tpl tslack : list byte) (ws : list (list byte)) (W arr lp x16 x24 x32 x40 can : word).

Local Notation FW := [(lo, S); (S + 88, S + 104)].

Hypothesis SSP : strspn_contract.
Hypothesis SCS : strcspn_contract.
Hypothesis ATOI : atoi_contract.
Hypothesis SNP : snprintf_contract.
Hypothesis SC : strcmp_contract.
Hypothesis LO : lo + 5936 <= S.
Hypothesis IE : 0x54f98 <= lo.
Hypothesis SPH : S < 2^63.
Hypothesis RR : 0 <= r <= 64.
Hypothesis NA : 0 < nargs < 2^31.
Hypothesis HAP : AP = bv_unsigned s4 + 8.
Hypothesis HT : ro_bytes_b rsegs T (tpl ++ NUL :: tslack) = true.
Hypothesis HTn : ~ In NUL tpl.
Hypothesis HTs : (- (T + Z.of_nat (length tpl) + 1)) mod 8 <= Z.of_nat (length tslack).
Hypothesis HTb : 0 <= T /\ T + Z.of_nat (length tpl) + 1 + Z.of_nat (length tslack) <= lo.
Hypothesis FR : rw_cells rsegs m0 (S + 8)
  [C8 (Z_to_bv 64 CW_TBL); C8 x16; C8 x24; C8 x32; C8 x40; C8 (Z_to_bv 64 0x1045f); C8 (Z_to_bv 64 AP); C8 W; C8 lp].
Hypothesis GG : bytes_at rsegs m0 0x22d40 (le8 (Z_to_bv 64 0x54730)).
Hypothesis GU : bytes_at rsegs m0 0x54730 (le8 can).
Hypothesis HNA : bytes_at rsegs m0 (bv_unsigned s4 + 4) (le4 (Z_to_bv 64 nargs)).
Hypothesis HNAd : disjoint_from FW (bv_unsigned s4 + 4) 4.
Hypothesis HWA : bytes_at rsegs m0 (bv_unsigned W + 16) (le8 arr).
Hypothesis HWAd : disjoint_from FW (bv_unsigned W + 16) 8.
Hypothesis HA1 : 0 < r -> bv_unsigned arr <> 0 /\ bv_unsigned arr mod 8 = 0.
Hypothesis HW : forall k, 0 <= k < r ->
  ptr_at m0 FW (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) ws []) /\ ~ In NUL (nth (Z.to_nat k) ws []).
Hypothesis HL : bytes_at rsegs m0 (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) /\ ~ In NUL (RecFacts.join_sp ws) /\
  disjoint_from FW (bv_unsigned lp) (Z.of_nat (length (RecFacts.join_sp ws)) + 1).
Hypothesis HLnz : bv_unsigned lp <> 0.
Hypothesis TMW : forall mc, munch FW m0 mc -> MemNorm.task_mem rsegs mc.

Definition cw_inv (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ munch FW m0 m /\ wmono rsegs m0 m /\ stk rsegs m lo S /\
  exists jb, rw_cells rsegs m (S + 88) [CB 16 jb].

Definition fprel (Fc : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k.

(* The item loop's registers: s0 = 8 a, s8 = a (the argument index), s10 = &args[a], s2 = ~&args[0],
   s5 = the template cursor T + k, s1 = r, s3 = the " " literal. *)
Abbreviation LS pc k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc m :=
  (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 (Z_to_bv 64 (8 * a)) (Z_to_bv 64 r) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (18446744073709551615 - AP)) (Z_to_bv 64 0x1034c) s4 (Z_to_bv 64 (T + Z.of_nat k)) xs6 xs7
           (Z_to_bv 64 a) s9 (Z_to_bv 64 (AP + 8 * a)) xs11 xt3 xt4 xt5 xt6)
      Fc (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

(* The join point 0x14e1c after an item whose text starts at template offset k: s7 = the item's length. *)
Definition ate1c (k : nat) (a : Z) : machine_state -> Prop := fun ms' =>
  exists (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs11 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms' = LS 0x14e1c k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6
            (Z_to_bv 64 (Z.of_nat (cspn_len SP1 (skipn k tpl)))) xs11 xt3 xt4 xt5 xt6 Fc fc m /\
    cw_inv m /\ frm0 fc /\ fprel Fc.

Lemma tp0 : forall mc A bs, munch FW m0 mc -> bytes_at rsegs m0 A bs ->
  disjoint_from FW A (Z.of_nat (length bs)) -> bytes_at rsegs mc A bs.
Proof. intros mc A bs MU H D. eapply bytes_at_transport; [exact H | exact MU | exact D]. Qed.

Lemma fr_at : forall mc, munch FW m0 mc -> wmono rsegs m0 mc ->
  rw_cells rsegs mc (S + 8)
    [C8 (Z_to_bv 64 CW_TBL); C8 x16; C8 x24; C8 x32; C8 x40; C8 (Z_to_bv 64 0x1045f); C8 (Z_to_bv 64 AP); C8 W; C8 lp].
Proof.
  intros mc MU WM. eapply rw_cells_transport; [exact FR | exact MU | exact WM |].
  cbn [disjoint_from cells_size csize Nat.add]. lia.
Qed.

Lemma gd_at : forall mc, munch FW m0 mc ->
  bytes_at rsegs mc 0x22d40 (le8 (Z_to_bv 64 0x54730)) /\ bytes_at rsegs mc 0x54730 (le8 can).
Proof.
  intros mc MU. split; (apply (tp0 mc); [exact MU | assumption | rewrite length_le8; cbn [disjoint_from]; lia]).
Qed.

Lemma na_at : forall mc, munch FW m0 mc -> ro_cells rsegs mc (bv_unsigned s4 + 4) [C4 (Z_to_bv 64 nargs)].
Proof. intros mc MU. apply bytes_ro4. apply (tp0 mc); [exact MU | exact HNA | rewrite length_le4; exact HNAd]. Qed.

Lemma wa_at : forall mc, munch FW m0 mc -> ro_cells rsegs mc (bv_unsigned W + 16) [C8 arr].
Proof. intros mc MU. apply bytes_ro8. apply (tp0 mc); [exact MU | exact HWA | rewrite length_le8; exact HWAd]. Qed.

Lemma ptr_tp : forall mc A s, munch FW m0 mc -> ptr_at m0 FW A s ->
  exists p : word, bytes_at rsegs mc A (le8 p) /\ disjoint_from FW A 8 /\ bv_unsigned p <> 0 /\
    bytes_at rsegs mc (bv_unsigned p) (s ++ [NUL]) /\ disjoint_from FW (bv_unsigned p) (Z.of_nat (length s) + 1).
Proof.
  intros mc A s MU (p & H1 & D1 & N & H2 & D2). exists p.
  split; [apply (tp0 mc); [exact MU | exact H1 | rewrite length_le8; exact D1]|].
  split; [exact D1|]. split; [exact N|].
  split; [apply (tp0 mc); [exact MU | exact H2 | rewrite length_app, Nat2Z.inj_add; exact D2]|]. exact D2.
Qed.

Lemma tpl_at : forall mc k, mem_inv rsegs mc -> (k <= length tpl)%nat ->
  bytes_at rsegs mc (T + Z.of_nat k) (skipn k tpl ++ NUL :: tslack).
Proof.
  intros mc k MI Hk.
  assert (H : bytes_at rsegs mc T (tpl ++ NUL :: tslack)).
  { apply lit_at; [exact MI | exact HT | lia | rewrite length_app; cbn [length]; lia]. }
  pose proof (bytes_at_skipn mc T _ k H ltac:(rewrite length_app; lia)) as H1.
  rewrite skipn_app in H1. replace (k - length tpl)%nat with 0%nat in H1 by lia. exact H1.
Qed.

Lemma tpl_at0 : forall mc k, mem_inv rsegs mc -> (k <= length tpl)%nat ->
  bytes_at rsegs mc (T + Z.of_nat k) (skipn k tpl ++ [NUL]).
Proof.
  intros mc k MI Hk. pose proof (tpl_at mc k MI Hk) as H.
  change (NUL :: tslack) with ([NUL] ++ tslack) in H. rewrite app_assoc in H.
  apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma tpl_rd : forall mc k, mem_inv rsegs mc -> (k <= length tpl)%nat ->
  ov_read_bytes rsegs mc (wa (T + Z.of_nat k)) 1 = Some [hd NUL (skipn k tpl)].
Proof.
  intros mc k MI Hk. apply (rd_hd mc T tpl tslack k); [|exact Hk].
  apply lit_at; [exact MI | exact HT | lia | rewrite length_app; cbn [length]; lia].
Qed.

Lemma sp_at : forall mc, mem_inv rsegs mc -> bytes_at rsegs mc 0x1034c (SP1 ++ [NUL]).
Proof. intros mc MI. apply lit_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.

Lemma empty_at : forall mc, mem_inv rsegs mc -> bytes_at rsegs mc 0x1045f ([] ++ [NUL]).
Proof. intros mc MI. apply lit_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.

Lemma pctd_at : forall mc, mem_inv rsegs mc -> bytes_at rsegs mc 0x10828 (pf_bytes ([37; 100] ++ [0])).
Proof. intros mc MI. apply lit_at; [exact MI | vm_compute; reflexivity | lia | cbn; lia]. Qed.

Lemma tpl_spn : forall zra zgp ztp zt0 zt1 zt2 zs0 zs1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
    zt3 zt4 zt5 zt6 Fc fc mc k,
  mem_inv rsegs mc -> stk rsegs mc lo S -> munch FW m0 mc -> (k <= length tpl)%nat ->
  evt rsegs (strspn_post zra (Z_to_bv 64 S) zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 Fc fc
               (skipn k tpl) SP1 lo mc)
    (MS (mkR zra (Z_to_bv 64 S) zgp ztp zt0 zt1 zt2 zs0 zs1 (Z_to_bv 64 (T + Z.of_nat k)) (Z_to_bv 64 0x1034c)
             za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
        Fc (Z_to_bv 64 STRSPN) fc None mc (seg_rom rsegs)).
Proof.
  intros zra zgp ztp zt0 zt1 zt2 zs0 zs1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
    zt3 zt4 zt5 zt6 Fc fc mc k MI ST MU Hk.
  destruct (gd_at mc MU) as [G1 G2].
  eapply SSP with (can := can).
  - rewrite unsigned_lit by lia. apply tpl_at0; assumption.
  - apply notin_skipn. exact HTn.
  - rewrite unsigned_lit by lia. apply sp_at. exact MI.
  - apply notin_nul_lit. vm_compute. reflexivity.
  - exact G1.
  - exact G2.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite !unsigned_lit by lia. rewrite length_skipn. left. lia.
  - rewrite unsigned_lit by lia. left. cbn. lia.
  - unfold SSP_GOT. left. lia.
  - unfold SSP_GUARD. left. lia.
  - exact MI.
Qed.

Lemma tpl_cspn : forall zra zgp ztp zt0 zt1 zt2 zs0 zs1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
    zt3 zt4 zt5 zt6 Fc fc mc k,
  mem_inv rsegs mc -> stk rsegs mc lo S -> munch FW m0 mc -> (k <= length tpl)%nat ->
  evt rsegs (strcspn_post zra (Z_to_bv 64 S) zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 Fc fc
               (skipn k tpl) SP1 lo mc)
    (MS (mkR zra (Z_to_bv 64 S) zgp ztp zt0 zt1 zt2 zs0 zs1 (Z_to_bv 64 (T + Z.of_nat k)) (Z_to_bv 64 0x1034c)
             za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 zt3 zt4 zt5 zt6)
        Fc (Z_to_bv 64 STRCSPN) fc None mc (seg_rom rsegs)).
Proof.
  intros zra zgp ztp zt0 zt1 zt2 zs0 zs1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
    zt3 zt4 zt5 zt6 Fc fc mc k MI ST MU Hk.
  destruct (gd_at mc MU) as [G1 G2].
  eapply SCS with (slack := tslack) (can := can).
  - rewrite unsigned_lit by lia. apply tpl_at; assumption.
  - apply notin_skipn. exact HTn.
  - intros _. rewrite unsigned_lit by lia. rewrite length_skipn.
    replace (T + Z.of_nat k + Z.of_nat (length tpl - k) + 1) with (T + Z.of_nat (length tpl) + 1) by lia. exact HTs.
  - rewrite unsigned_lit by lia. apply sp_at. exact MI.
  - apply notin_nul_lit. vm_compute. reflexivity.
  - exact G1.
  - exact G2.
  - rewrite unsigned_lit by lia. exact ST.
  - rewrite unsigned_lit by lia. lia.
  - rewrite !unsigned_lit by lia. rewrite length_skipn. left. lia.
  - rewrite unsigned_lit by lia. left. cbn. lia.
  - unfold CSPN_SSP_GOT. left. lia.
  - unfold CSPN_SSP_GUARD. left. lia.
  - exact MI.
Qed.

Lemma inv_pack : forall m jb, mem_inv rsegs m -> munch FW m0 m -> wmono rsegs m0 m -> stk rsegs m lo S ->
  rw_cells rsegs m (S + 88) [CB 16 jb] -> cw_inv m.
Proof. intros m jb H1 H2 H3 H4 H5. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists jb. exact H5. Qed.

Lemma ap_lt : forall a y, ptr_at m0 FW (AP + 8 * a) y -> AP + 8 * a + 8 <= 2 ^ 64.
Proof. intros a y (p & H & _). pose proof (bytes_at_bound _ _ _ _ H) as B. rewrite length_le8 in B. lia. Qed.

(* 0x14e04: the argument at s10 against the expected string at s6 (both y), then the join point. *)
Lemma cmp_e04 : forall k1 a q y xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> 0 <= a < nargs ->
  bytes_at rsegs mc (bv_unsigned q) (y ++ [NUL]) -> ~ In NUL y -> ptr_at m0 FW (AP + 8 * a) y ->
  evt rsegs (ate1c k1 a)
    (LS 0x14e04 k1 a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 q
        (Z_to_bv 64 (Z.of_nat (cspn_len SP1 (skipn k1 tpl)))) xs11 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k1 a q y xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 Fc fc mc
    HI FRM FP Ha HQ HQn HA.
  pose proof HI as (MI & MU & WM & ST & jb & BUF).
  pose proof (ap_lt a y HA) as APL.
  pose proof (bv_unsigned_in_range 64 s4) as Rs4. unfold bv_modulus in Rs4.
  destruct (ptr_tp mc _ _ MU HA) as (p & HP & HPd & HP0 & HPs & HPsd).
  assert (RK : ov_read_bytes rsegs mc (wa (AP + 8 * a)) 8 = Some (le8 p)).
  { replace (wa (AP + 8 * a)) with (wa (AP + 8 * a + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs mc _ (le8 p) 0 8 HP ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  zstep. if_cases HO.
  { exfalso. zc HO. lia. }
  zstep. zstep. if_cases HZ.
  { exfalso. zify_cond HZ. lia. }
  zstep. zstep.
  eapply evt_cut.
  { eapply SC with (sx := y) (sy := y); [exact HPs | exact HQn | exact HQ | exact HQn]. }
  intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
  fix_ret.
  assert (R0 : rr = Z_to_bv 64 0) by (apply Hrr; reflexivity). subst rr.
  zstep. if_cases HZ2; [exfalso; vm_compute in HZ2; discriminate HZ2|].
  apply evt_done. unfold ate1c. do 21 eexists. split; [reflexivity|]. split; [exact HI|]. split; [exact FRM | exact FP].
Qed.

(* 0x14de8 with s6 = q, the expected string y: skip the item (strcspn), then compare. *)
Lemma cmp_de8 : forall k1 a q y xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> 0 <= a < nargs -> (k1 <= length tpl)%nat -> bv_unsigned q <> 0 ->
  bytes_at rsegs mc (bv_unsigned q) (y ++ [NUL]) -> ~ In NUL y ->
  (bv_unsigned q + Z.of_nat (length y) + 1 <= S - 96 \/ S <= bv_unsigned q) ->
  ptr_at m0 FW (AP + 8 * a) y ->
  evt rsegs (ate1c k1 a)
    (LS 0x14de8 k1 a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 q xs7
        (Z_to_bv 64 (18446744073709551615 - (T + Z.of_nat k1))) xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k1 a q y xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 Fc fc mc
    HI FRM FP Ha Hk HQ0 HQ HQn HQd HA.
  destruct HI as (MI & MU & WM & ST & jb & BUF).
  zstep. zstep. zstep. zstep.
  eapply evt_cut; [eapply tpl_cspn; [exact MI | exact ST | exact MU | exact Hk] |].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1 & ST1).
  subst ms'. rewrite unsigned_lit in MU1, ST1 by lia.
  after_call MU1 WM1. try clear MI. clear MU1 WM1.
  fix_ret.
  pose proof (cspn_le (skipn k1 tpl)) as CL. rewrite length_skipn in CL.
  zstep. if_cases HO.
  { exfalso. zc HO. lia. }
  zstep. zstep. if_cases HZ.
  { exfalso. zify_cond HZ. lia. }
  eapply cmp_e04; [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | exact HQ | exact HQn | exact HA].
Qed.

(* 0x14de8 with s6 = 0: an item with no compare; skip it. *)
Lemma skip_de8 : forall k1 a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> (k1 <= length tpl)%nat ->
  evt rsegs (ate1c k1 a)
    (LS 0x14de8 k1 a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 0) xs7
        (Z_to_bv 64 (18446744073709551615 - (T + Z.of_nat k1))) xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k1 a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 Fc fc mc HI FRM FP Hk.
  destruct HI as (MI & MU & WM & ST & jb & BUF).
  zstep. zstep. zstep. zstep.
  eapply evt_cut; [eapply tpl_cspn; [exact MI | exact ST | exact MU | exact Hk] |].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1 & ST1).
  subst ms'. rewrite unsigned_lit in MU1, ST1 by lia.
  after_call MU1 WM1. try clear MI. clear MU1 WM1.
  fix_ret.
  pose proof (cspn_le (skipn k1 tpl)) as CL. rewrite length_skipn in CL.
  zstep. if_cases HO.
  { exfalso. zc HO. lia. }
  zstep. zstep. if_cases HZ; [|exfalso; vm_compute in HZ; discriminate HZ].
  apply evt_done. unfold ate1c. do 21 eexists. split; [reflexivity|].
  split; [eapply inv_pack; eassumption|]. split; [exact FRM | exact FP].
Qed.

Lemma p_d3c : forall k1 a bb v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> 0 <= a < nargs -> (k1 <= length tpl)%nat ->
  0 <= v < 2^31 -> 0 <= bb < 256 ->
  (forall y, want r ws (kind_item bb v) = Some y -> ptr_at m0 FW (AP + 8 * a) y) ->
  evt rsegs (ate1c k1 a)
    (LS 0x14d3c k1 a xra xt0 xt1 xt2 (Z_to_bv 64 v) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 (Z_to_bv 64 bb)
        (Z_to_bv 64 (18446744073709551615 - (T + Z.of_nat k1))) xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k1 a bb v xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 Fc fc mc
    HI FRM FP Ha Hk Hv Hbb HC.
  pose proof HI as (MI & MU & WM & ST & jb & BUF).
  pose proof (fr_at mc MU WM) as FRc.
  zstep. if_cases C.
  - zc C. rewrite ?signed_lit in C by lia.
    destruct (HW v ltac:(lia)) as [HWv HWn].
    destruct (HA1 ltac:(lia)) as [ANZ AAL].
    destruct (ptr_tp mc _ _ MU HWv) as (p & HP & HPd & HP0 & HPs & HPsd).
    pose proof (wa_at mc MU) as WAc.
    pose proof (bytes_at_bound _ _ _ _ HP) as HPB. rewrite length_le8 in HPB.
    pose proof (bv_unsigned_in_range 64 arr) as Rarr. unfold bv_modulus in Rarr.
    assert (SH : Z.shiftl v 3 = 8 * v) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (RK : ov_read_bytes rsegs mc (wa (bv_unsigned arr + Z.shiftl v 3)) 8 = Some (le8 p)).
    { rewrite SH.
      replace (wa (bv_unsigned arr + 8 * v)) with (wa (bv_unsigned arr + 8 * v + 0)) by (f_equal; lia).
      rewrite (bytes_at_read rsegs mc _ (le8 p) 0 8 HP ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
    assert (AL8 : (bv_unsigned arr + Z.shiftl v 3) mod 8 = 0).
    { rewrite SH. replace (bv_unsigned arr + 8 * v) with (bv_unsigned arr + v * 8) by lia.
      rewrite Z.mod_add by lia. exact AAL. }
    assert (E1 : (0 <? bv_unsigned arr) = true) by (apply Z.ltb_lt; lia).
    assert (E2 : ((bv_unsigned arr + Z.shiftl v 3) mod 18446744073709551616 <? 1) = false)
      by (apply Z.ltb_ge; rewrite SH, Z.mod_small by lia; lia).
    assert (E2' : (bv_unsigned arr + Z.shiftl v 3 <? 1) = false) by (apply Z.ltb_ge; rewrite SH; lia).
    assert (E3 : ((bv_unsigned arr + Z.shiftl v 3) mod 18446744073709551616 <? bv_unsigned arr) = false)
      by (apply Z.ltb_ge; rewrite SH, Z.mod_small by lia; lia).
    assert (E3' : (bv_unsigned arr + Z.shiftl v 3 <? bv_unsigned arr) = false) by (apply Z.ltb_ge; rewrite SH; lia).
    assert (E4 : (Z.lxor v 9223372036854775808 <? 9223372036854775808) = false).
    { apply Z.ltb_ge. change 9223372036854775808 with (2 ^ 63). rewrite zb_lxor_pow2_small by lia. lia. }
    do 13 zstep.
    rewrite ?E1, ?E2, ?E2', ?E3, ?E3', ?E4.
    zstep. if_cases B35.
    + zc B35.
      zstep. if_cases HB2; [exfalso; vm_compute in HB2; discriminate HB2|].
      zstep. if_cases HB1; [exfalso; zc HB1; lia|].
      zstep. zb_masks. rewrite ?AL8.
      zstep. if_cases HAL; [exfalso; first [vm_compute in HAL; discriminate HAL | zc HAL; lia]|].
      zstep.
      assert (W1 : want r ws (kind_item bb v) = Some (nth (Z.to_nat v) ws [])).
      { unfold kind_item, want. rewrite (proj2 (Z.eqb_neq bb 35)) by lia.
        destruct (bb =? 63); rewrite (proj2 (Z.ltb_lt v r)) by lia; reflexivity. }
      eapply cmp_de8; [exact HI | exact FRM | exact FP | exact Ha | exact Hk | exact HP0 | exact HPs | exact HWn
                     | | apply HC; exact W1].
      cbn [disjoint_from] in HPsd. lia.
    + zc B35. assert (EB : bb = 35) by lia. subst bb.
      zstep. if_cases HB2; [exfalso; vm_compute in HB2; discriminate HB2|].
      zstep. if_cases HB1; [exfalso; zc HB1; lia|].
      zstep. zb_masks. rewrite ?AL8.
      zstep. if_cases HAL; [exfalso; first [vm_compute in HAL; discriminate HAL | zc HAL; lia]|].
      zstep. zstep.
      set (w := nth (Z.to_nat v) ws []) in *.
      rewrite <- (Z_to_bv_bv_unsigned p).
      eapply evt_cut; [eapply ATOI with (A := bv_unsigned p) (str := w); [exact HPs | exact MI] |].
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MU1 & WM1 & MI1).
      subst ms'.
      after_call MU1 WM1. try clear MI. clear MU1 WM1.
      fix_ret.
      pose proof (atoi_val_range w) as AR.
      pose proof (pf_dec_len (atoi_val w) AR) as TL.
      set (Tn := pf_dec (atoi_val w)) in *.
      destruct (rw_cells_cb_inv _ _ _ _ BUF) as (BB & BW & BL).
      pose proof (bytes_at_skipn _ _ _ (length Tn + 1) BB ltac:(lia)) as BT.
      clear BB.
      destruct (gd_at m1 MU) as [G1 G2].
      pose proof (pctd_at m1 MI1) as PF.
      do 7 zstep.
      eapply evt_cut.
      { eapply SNP with (fmt := [37; 100]) (ps := [Pd]) (args := [AInt (atoi_val w)]) (T := Tn)
                        (junk := jb) (lo := lo) (canary := can).
        - rewrite unsigned_lit by lia. exact PF.
        - rewrite unsigned_lit by lia. unfold RO_LO. lia.
        - rewrite unsigned_lit by lia. unfold RO_END. cbn [length Z.of_nat]. lia.
        - reflexivity.
        - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact AR|].
          rewrite unsigned_lit_wrap. apply mod64_32.
        - cbn [pf_text option_map]. rewrite app_nil_r. reflexivity.
        - rewrite !unsigned_lit by lia. exact BUF.
        - rewrite unsigned_lit by lia. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - right. rewrite !unsigned_lit by lia. lia.
        - apply img_free_hi. rewrite unsigned_lit by lia. lia.
        - rewrite unsigned_lit by lia. exact ST.
        - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
        - unfold snprintf_c.IMG_END. lia.
        - rewrite unsigned_lit by lia. lia.
        - exact FRM.
        - exact MI1.
        - exact (TMW m1 MU).
        - exact G1.
        - exact G2. }
      intros ms' PO. unfold printf_post in PO. rewrite !unsigned_lit in PO by lia.
      rewrite firstn_all2 in PO by lia.
      destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' &
                      Ft & fc' & m2 & E & MU2 & WM2 & MI2 & _ & FRM2 & FP2 & ST2 & DB2).
      subst ms'.
      fix_ret.
      pose proof (fp_chain F Fc Ft FP FP2) as FP3.
      clear PF G1 G2.
      after_call MU2 WM2. try clear MI1. clear MU2 WM2.
      assert (BUF2 : rw_cells rsegs m2 (S + 88) [CB 16 (pf_bytes (Tn ++ [0]) ++ skipn (length Tn + 1) jb)]).
      { apply rw_cells_cbn; [| exact BW |].
        - apply bytes_at_app. split; [exact DB2|].
          rewrite length_pf_bytes, length_app. cbn [length]. exact BT.
        - rewrite length_app, length_pf_bytes, length_app, length_skipn. cbn [length]. lia. }
      zstep.
      assert (W1 : want r ws (kind_item 35 v) = Some (pf_bytes Tn)).
      { unfold kind_item, want. cbn [Z.eqb Pos.eqb]. rewrite (proj2 (Z.ltb_lt v r)) by lia. reflexivity. }
      eapply cmp_de8 with (y := pf_bytes Tn).
      * eapply inv_pack; [exact MI2 | exact MU | exact WM | exact ST2 | exact BUF2].
      * exact FRM2.
      * exact FP3.
      * exact Ha.
      * exact Hk.
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia. rewrite <- pf_bytes_nul. exact DB2.
      * apply notin_nul_pf, pf_dec_nz.
      * right. rewrite unsigned_lit by lia. lia.
      * apply HC. exact W1.
  - zc C. rewrite ?signed_lit in C by lia.
    assert (E5 : (Z.lxor v 9223372036854775808 <? Z.lxor r 9223372036854775808) = false).
    { apply Z.ltb_ge. change 9223372036854775808 with (2 ^ 63). rewrite !zb_lxor_pow2_small by lia. lia. }
    assert (E6 : ((bb + -63) mod 18446744073709551616 <? 1) = (bb =? 63)).
    { destruct (Z.eqb_spec bb 63) as [->|N]; [reflexivity|]. apply Z.ltb_ge.
      destruct (Z_lt_ge_dec bb 63).
      - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
      - rewrite Z.mod_small by lia. lia. }
    do 9 zstep.
    rewrite E5, E6.
    destruct (Z.eqb_spec bb 63) as [E63|N63].
    + match goal with |- context [Z_to_bv 64 (Z.land ?x 66655)] =>
        replace (Z_to_bv 64 (Z.land x 66655)) with (Z_to_bv 64 0) by reflexivity end.
      eapply skip_de8; [exact HI | exact FRM | exact FP | exact Hk].
    + match goal with |- context [Z_to_bv 64 (Z.land ?x 66655)] =>
        replace (Z_to_bv 64 (Z.land x 66655)) with (Z_to_bv 64 66655) by reflexivity end.
      assert (W0 : want r ws (kind_item bb v) = Some []).
      { unfold kind_item, want. rewrite (proj2 (Z.eqb_neq bb 63)) by exact N63.
        destruct (bb =? 35); rewrite (proj2 (Z.ltb_ge v r)) by lia; reflexivity. }
      eapply cmp_de8 with (y := []); [exact HI | exact FRM | exact FP | exact Ha | exact Hk | | | | | apply HC; exact W0].
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia. apply empty_at. exact MI.
      * intros H. inversion H.
      * left. rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
Qed.

(* 0x14d30: atoi of the item's digits at template offset k1 + d (d = 1 past a '#' or '?'), then 0x14d3c. *)
Lemma p_d30 : forall k1 a d bb xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> 0 <= a < nargs -> (k1 + d <= length tpl)%nat -> (d <= 1)%nat -> 0 <= bb < 256 ->
  item_ok (kind_item bb (atoi_val (skipn (k1 + d) tpl))) ->
  (forall y, want r ws (kind_item bb (atoi_val (skipn (k1 + d) tpl))) = Some y -> ptr_at m0 FW (AP + 8 * a) y) ->
  evt rsegs (ate1c k1 a)
    (LS 0x14d30 k1 a xra xt0 xt1 xt2 (Z_to_bv 64 (Z.of_nat d)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 (Z_to_bv 64 bb)
        (Z_to_bv 64 (18446744073709551615 - (T + Z.of_nat k1))) xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k1 a d bb xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xt3 xt4 xt5 xt6 Fc fc mc
    HI FRM FP Ha Hk Hd Hbb HK HC.
  pose proof HI as (MI & MU & WM & ST & jb & BUF).
  zstep. if_cases HO.
  { exfalso. zc HO. lia. }
  zstep. zstep.
  replace (Z_to_bv 64 (T + Z.of_nat k1 + Z.of_nat d)) with (Z_to_bv 64 (T + Z.of_nat (k1 + d))) by (f_equal; lia).
  eapply evt_cut; [eapply ATOI with (A := T + Z.of_nat (k1 + d)) (str := skipn (k1 + d) tpl);
                   [apply tpl_at0; [exact MI | exact Hk] | exact MI] |].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1).
  subst ms'.
  after_call MU1 WM1. try clear MI. clear MU1 WM1.
  fix_ret.
  pose proof (atoi_val_range (skipn (k1 + d) tpl)) as AR.
  eapply p_d3c; [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | lia | | exact Hbb | exact HC].
  unfold kind_item, item_ok in HK. destruct (bb =? 35), (bb =? 63); lia.
Qed.

(* The template cursor after the spaces before item k's text, and after the item. *)
Definition kp (k : nat) : nat := k + spn_len SP1 (skipn k tpl).
Definition kn (k : nat) : nat := kp k + cspn_len SP1 (skipn (kp k) tpl).

Lemma skipn_kp : forall k, skipn (spn_len SP1 (skipn k tpl)) (skipn k tpl) = skipn (kp k) tpl.
Proof. intros k. unfold kp. rewrite skipn_skipn, Nat.add_comm. reflexivity. Qed.

Lemma skipn_kn : forall k, skipn (cspn_len SP1 (skipn (kp k) tpl)) (skipn (kp k) tpl) = skipn (kn k) tpl.
Proof. intros k. unfold kn. rewrite skipn_skipn, Nat.add_comm. reflexivity. Qed.

Lemma kn_gt : forall k, (k < length tpl)%nat -> (k < kn k <= length tpl)%nat.
Proof.
  intros k LT. unfold kn, kp.
  pose proof (spn_le (skipn k tpl)) as H1. pose proof (cspn_le (skipn (k + spn_len SP1 (skipn k tpl)) tpl)) as H2.
  rewrite length_skipn in H1, H2.
  assert (NE : skipn k tpl <> []) by (rewrite (hd_skipn_S tpl k LT); discriminate).
  pose proof (adv_ge1 (skipn k tpl) NE) as H3. rewrite skipn_skipn, (Nat.add_comm _ k) in H3. lia.
Qed.

Lemma seqz63 : forall bb, 0 <= bb < 256 -> ((bb + -63) mod 18446744073709551616 <? 1) = (bb =? 63).
Proof.
  intros bb Hbb. destruct (Z.eqb_spec bb 63) as [->|N]; [reflexivity|]. apply Z.ltb_ge.
  destruct (Z_lt_ge_dec bb 63).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite Z.mod_small by lia. lia.
Qed.

(* One item, 0x14cd4 to the join point 0x14e1c. *)
Lemma item_step : forall k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc,
  cw_inv mc -> frm0 fc -> fprel Fc -> 0 <= a < nargs -> (k < length tpl)%nat ->
  item_ok (item_of (skipn (kp k) tpl)) ->
  (forall y, want r ws (item_of (skipn (kp k) tpl)) = Some y -> ptr_at m0 FW (AP + 8 * a) y) ->
  evt rsegs (ate1c (kp k) a)
    (LS 0x14cd4 k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  intros k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc
    HI FRM FP Ha Hk HK HC.
  pose proof HI as (MI & MU & WM & ST & jb & BUF).
  pose proof (tpl_rd mc k MI ltac:(lia)) as RD.
  pose proof (hd_nz tpl k HTn Hk) as NZ.
  pose proof (byte_range (hd NUL (skipn k tpl))) as BR.
  zstep. zstep. if_cases Q.
  { exfalso. zc Q. lia. }
  clear RD.
  zstep. zstep. zstep.
  eapply evt_cut; [eapply tpl_spn; [exact MI | exact ST | exact MU | lia] |].
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
              E & MU1 & WM1 & MI1 & ST1).
  subst ms'. rewrite unsigned_lit in MU1, ST1 by lia.
  after_call MU1 WM1. try clear MI. clear MU1 WM1.
  fix_ret.
  pose proof (spn_le (skipn k tpl)) as SL. rewrite length_skipn in SL.
  assert (KP : (kp k <= length tpl)%nat) by (unfold kp; lia).
  zstep. rewrite ?zb_lxor_ones by lia. zstep. if_cases HO.
  { exfalso. zc HO. lia. }
  zstep.
  replace (Z_to_bv 64 (T + Z.of_nat k + Z.of_nat (spn_len SP1 (skipn k tpl))))
    with (Z_to_bv 64 (T + Z.of_nat (kp k))) by (unfold kp; f_equal; lia).
  pose proof (tpl_rd m1 (kp k) MI1 KP) as RD2.
  pose proof (byte_range (hd NUL (skipn (kp k) tpl))) as BR2.
  pose proof (fr_at m1 MU WM) as FRc.
  zstep. zstep.
  rewrite ?zb_lxor_ones by lia.
  zstep. zstep. if_cases Q1.
  - zc Q1.
    pose proof (hd_nz_lt tpl (kp k) ltac:(lia)) as LT.
    rewrite (item_of_num _ Q1), tl_skipn in HK, HC.
    zstep.
    change (Z_to_bv 64 1) with (Z_to_bv 64 (Z.of_nat 1)).
    eapply p_d30 with (d := 1%nat); [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | lia | lia | lia | |].
    + rewrite Nat.add_1_r. exact HK.
    + rewrite Nat.add_1_r. exact HC.
  - zc Q1.
    zstep. zstep. if_cases Q2.
    + zc Q2. zstep. zstep.
      eapply skip_de8; [eapply inv_pack; eassumption | exact FRM | exact FP | exact KP].
    + zc Q2.
      zstep. zstep. zstep. if_cases Q3.
      * zc Q3.
        rewrite (item_of_line _ Q3) in HC.
        destruct HL as (HL1 & HL2 & HL3).
        eapply cmp_de8 with (y := RecFacts.join_sp ws);
          [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | exact KP | exact HLnz | | exact HL2 | |
           apply HC; reflexivity].
        { apply (tp0 m1); [exact MU | exact HL1 | rewrite length_app, Nat2Z.inj_add; exact HL3]. }
        { cbn [disjoint_from] in HL3. lia. }
      * zc Q3.
        zstep. zstep. zstep.
        rewrite ?(seqz63 (bv_unsigned (hd NUL (skipn (kp k) tpl)))) by lia.
        destruct (Z.eqb_spec (bv_unsigned (hd NUL (skipn (kp k) tpl))) 63) as [E63|N63].
        -- pose proof (hd_nz_lt tpl (kp k) ltac:(lia)) as LT.
           rewrite (item_of_opt _ E63), tl_skipn in HK, HC.
           change (Z_to_bv 64 (Z.b2z true)) with (Z_to_bv 64 (Z.of_nat 1)).
           eapply p_d30 with (d := 1%nat); [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | lia | lia | lia
                                           | |].
           ++ rewrite Nat.add_1_r. exact HK.
           ++ rewrite Nat.add_1_r. exact HC.
        -- rewrite (item_of_word _ Q1 Q2 Q3 N63) in HK, HC.
           change (Z_to_bv 64 (Z.b2z false)) with (Z_to_bv 64 (Z.of_nat 0)).
           eapply p_d30 with (d := 0%nat); [eapply inv_pack; eassumption | exact FRM | exact FP | exact Ha | lia | lia | lia
                                           | |].
           ++ rewrite Nat.add_0_r. exact HK.
           ++ rewrite Nat.add_0_r. exact HC.
Qed.

(* The loop's exit 0x14e34. *)
Definition at_exit : machine_state -> Prop := fun ms' =>
  exists (k : nat) (a : Z) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    ms' = LS 0x14e34 k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc m /\
    cw_inv m /\ frm0 fc /\ fprel Fc.

(* What each remaining item needs: item j of the list is compared with argument a + j. *)
Definition items_pre (a : Z) (its : list witem) : Prop :=
  forall j i, nth_error its j = Some i -> a + Z.of_nat j < nargs ->
    item_ok i /\ forall y, want r ws i = Some y -> ptr_at m0 FW (AP + 8 * (a + Z.of_nat j)) y.

Lemma loop : forall n k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc,
  (length tpl - k < n)%nat -> (k <= length tpl)%nat -> 0 <= a < nargs ->
  cw_inv mc -> frm0 fc -> fprel Fc -> items_pre a (tpl_items n (skipn k tpl)) ->
  evt rsegs at_exit (LS 0x14cd4 k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc).
Proof.
  induction n as [|n IH];
    intros k a xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 Fc fc mc HN Hk Ha HI FRM FP HP;
    [lia|].
  destruct (Nat.lt_ge_cases k (length tpl)) as [LT|GE].
  - assert (NE : skipn k tpl <> []) by (rewrite (hd_skipn_S tpl k LT); discriminate).
    rewrite (tpl_items_cons n _ NE), skipn_kp, skipn_kn in HP.
    destruct (HP 0%nat _ eq_refl ltac:(lia)) as [HK HC].
    rewrite Z.add_0_r in HC.
    pose proof (kn_gt k LT) as KG.
    eapply evt_cut; [eapply item_step; [exact HI | exact FRM | exact FP | exact Ha | exact LT | exact HK | exact HC] |].
    intros ms' (yra & yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ys6 & ys11 & yt3 & yt4 & yt5 & yt6 &
                Fc' & fc' & m' & E & HI' & FRM' & FP').
    subst ms'.
    pose proof HI' as (MI' & MU' & WM' & _).
    pose proof (na_at m' MU') as NAc.
    pose proof (cspn_le (skipn (kp k) tpl)) as CL. rewrite length_skipn in CL.
    assert (KP : (kp k <= length tpl)%nat) by (unfold kn in KG; lia).
    zstep. rewrite (sx32_lit nargs) by lia.
    zstep.
    replace (Z_to_bv 64 (T + Z.of_nat (kp k) + Z.of_nat (cspn_len SP1 (skipn (kp k) tpl))))
      with (Z_to_bv 64 (T + Z.of_nat (kn k))) by (unfold kn; f_equal; lia).
    zstep. zstep. zstep.
    replace (Z_to_bv 64 (AP + 8 * a + 8)) with (Z_to_bv 64 (AP + 8 * (a + 1))) by (f_equal; lia).
    replace (Z_to_bv 64 (8 * a + 8)) with (Z_to_bv 64 (8 * (a + 1))) by (f_equal; lia).
    zstep. if_cases Q.
    + zc Q. rewrite ?signed_lit in Q by lia.
      eapply IH; [lia | lia | lia | exact HI' | exact FRM' | exact FP' |].
      intros j i Hj Hja. destruct (HP (Datatypes.S j) i Hj ltac:(lia)) as [H1 H2]. split; [exact H1|].
      replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (Datatypes.S j)) by lia. exact H2.
    + apply evt_done. unfold at_exit. do 24 eexists. split; [reflexivity|].
      split; [exact HI'|]. split; [exact FRM' | exact FP'].
  - pose proof HI as (MI & MU & WM & ST & jb & BUF).
    pose proof (tpl_rd mc k MI Hk) as RD.
    rewrite (hd_skipn_end tpl k GE) in RD.
    zstep. zstep. if_cases Q.
    + apply evt_done. unfold at_exit. do 24 eexists. split; [reflexivity|].
      split; [exact HI|]. split; [exact FRM | exact FP].
    + exfalso. vm_compute in Q. discriminate Q.
Qed.

End CW.

(* The state at the item loop's exit 0x14e34: the frame and callee-saved registers as at entry, s1 = r,
   s3 = the " " literal; memory changed only below sp and in the number buffer sp+88. *)
Definition cw_items_post (gp tp s4 s9 : word) (F : bvmap 5 word) (m0 : word -> option byte) (lo S r : Z)
    : machine_state -> Prop := fun ms' =>
  exists (xra xt0 xt1 xt2 xs0 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (jb : list byte),
    ms' = MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                  xs2 (Z_to_bv 64 0x1034c) s4 xs5 xs6 xs7 xs8 s9 xs10 xs11 xt3 xt4 xt5 xt6)
             Fc (Z_to_bv 64 0x14e34) fc None m (seg_rom rsegs) /\
    mem_inv rsegs m /\ munch [(lo, S); (S + 88, S + 104)] m0 m /\ wmono rsegs m0 m /\ stk rsegs m lo S /\
    rw_cells rsegs m (S + 88) [CB 16 jb] /\ frm0 fc /\
    (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k).

(* check_words from 0x14cb4 (nargs > 0, a0 = 8 fn, s4 = the call) to the item loop's exit 0x14e34: every
   argument the verb's template compares is equal to its expected string. *)
Theorem cw_items_loop :
  strspn_contract -> strcspn_contract -> atoi_contract -> snprintf_contract -> strcmp_contract ->
  forall (gp tp s4 s9 : word) (F : bvmap 5 word) (m0 : word -> option byte) (lo S nargs r fn : Z)
         (ws : list (list byte)) (W arr lp x16 x24 x32 x40 can : word)
         (xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 : word)
         (Fc : bvmap 5 word) (fc : bv 32) (mc : word -> option byte) (jb : list byte),
  lo + 5936 <= S -> 0x54f98 <= lo -> S < 2^63 -> 0 <= r <= 64 -> 0 < nargs < 2^31 -> 0 <= fn < 26 ->
  bv_unsigned s4 + 64 <= 2 ^ 64 ->
  rw_cells rsegs m0 (S + 8)
    [C8 (Z_to_bv 64 CW_TBL); C8 x16; C8 x24; C8 x32; C8 x40; C8 (Z_to_bv 64 0x1045f);
     C8 (Z_to_bv 64 (bv_unsigned s4 + 8)); C8 W; C8 lp] ->
  bytes_at rsegs m0 (CW_TBL + 8 * fn) (le8 (Z_to_bv 64 (cw_tp fn))) ->
  bytes_at rsegs m0 0x22d40 (le8 (Z_to_bv 64 0x54730)) -> bytes_at rsegs m0 0x54730 (le8 can) ->
  bytes_at rsegs m0 (bv_unsigned s4 + 4) (le4 (Z_to_bv 64 nargs)) ->
  disjoint_from [(lo, S); (S + 88, S + 104)] (bv_unsigned s4 + 4) 4 ->
  bytes_at rsegs m0 (bv_unsigned W + 16) (le8 arr) -> disjoint_from [(lo, S); (S + 88, S + 104)] (bv_unsigned W + 16) 8 ->
  (0 < r -> bv_unsigned arr <> 0 /\ bv_unsigned arr mod 8 = 0) ->
  (forall k, 0 <= k < r -> ptr_at m0 [(lo, S); (S + 88, S + 104)] (bv_unsigned arr + 8 * k) (nth (Z.to_nat k) ws []) /\
     ~ In NUL (nth (Z.to_nat k) ws [])) ->
  bytes_at rsegs m0 (bv_unsigned lp) (RecFacts.join_sp ws ++ [NUL]) -> ~ In NUL (RecFacts.join_sp ws) ->
  disjoint_from [(lo, S); (S + 88, S + 104)] (bv_unsigned lp) (Z.of_nat (length (RecFacts.join_sp ws)) + 1) ->
  bv_unsigned lp <> 0 ->
  (forall a i, 0 <= a < nargs -> nth_error (call_items fn) (Z.to_nat a) = Some i ->
     forall y, want r ws i = Some y -> ptr_at m0 [(lo, S); (S + 88, S + 104)] (bv_unsigned s4 + 8 + 8 * a) y) ->
  (forall mc', munch [(lo, S); (S + 88, S + 104)] m0 mc' -> MemNorm.task_mem rsegs mc') ->
  mem_inv rsegs mc -> munch [(lo, S); (S + 88, S + 104)] m0 mc -> wmono rsegs m0 mc -> stk rsegs mc lo S ->
  rw_cells rsegs mc (S + 88) [CB 16 jb] -> frm0 fc ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k) ->
  evt rsegs (cw_items_post gp tp s4 s9 F m0 lo S r)
    (MS (mkR xra (Z_to_bv 64 S) gp tp xt0 xt1 xt2 xs0 (Z_to_bv 64 r) (Z_to_bv 64 (8 * fn)) xa1 xa2 xa3 xa4 xa5
             xa6 xa7 xs2 (Z_to_bv 64 0x1034c) s4 xs5 xs6 xs7 xs8 s9 xs10 xs11 xt3 xt4 xt5 xt6)
        Fc (Z_to_bv 64 0x14cb4) fc None mc (seg_rom rsegs)).
Proof.
  intros SSP SCS ATOI SNP SC gp tp s4 s9 F m0 lo S nargs r fn ws W arr lp x16 x24 x32 x40 can
    xra xt0 xt1 xt2 xs0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 Fc fc mc jb
    LO IE SPH RR NA HFN S4B FR HTB GG GU HNA HNAd HWA HWAd HA1 HW HL1 HL2 HL3 HLnz HARGS TMW MI MU WM ST BUF FRM FP.
  destruct (cw_tpl_facts fn HFN) as (F1 & F2 & F3 & F4).
  apply andb_prop in F3. destruct F3 as [F3a F3b]. apply Z.leb_le in F3a, F3b, F2.
  pose proof (bv_unsigned_in_range 64 s4) as Rs4. unfold bv_modulus in Rs4.
  assert (TB : ro_cells rsegs mc (CW_TBL + 8 * fn) [C8 (Z_to_bv 64 (cw_tp fn))]).
  { apply bytes_ro8. eapply bytes_at_transport; [exact HTB | exact MU |].
    rewrite length_le8. cbn [disjoint_from]. unfold CW_TBL. lia. }
  assert (FRc : rw_cells rsegs mc (S + 8)
                  [C8 (Z_to_bv 64 CW_TBL); C8 x16; C8 x24; C8 x32; C8 x40; C8 (Z_to_bv 64 0x1045f);
                   C8 (Z_to_bv 64 (bv_unsigned s4 + 8)); C8 W; C8 lp]).
  { eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. lia. }
  zstep. zstep. zstep. zstep.
  assert (RT : ov_read_bytes rsegs mc (wa (CW_TBL + 8 * fn)) 8 = Some (le8 (Z_to_bv 64 (cw_tp fn)))).
  { assert (HB : bytes_at rsegs mc (CW_TBL + 8 * fn) (le8 (Z_to_bv 64 (cw_tp fn)))).
    { eapply bytes_at_transport; [exact HTB | exact MU |]. rewrite length_le8. cbn [disjoint_from]. unfold CW_TBL. lia. }
    replace (wa (CW_TBL + 8 * fn)) with (wa (CW_TBL + 8 * fn + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs mc _ _ 0 8 HB ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  zstep. zstep. zstep. zstep.
  rewrite ?(Z.mod_small (bv_unsigned s4 + 8)) by lia. rewrite zb_lxor_ones by lia.
  replace (Z_to_bv 64 (cw_tp fn)) with (Z_to_bv 64 (cw_tp fn + Z.of_nat 0)) by (f_equal; lia).
  replace (Z_to_bv 64 (bv_unsigned s4 + 8)) with (Z_to_bv 64 (bv_unsigned s4 + 8 + 8 * 0)) by (f_equal; lia).
  eapply evt_mono.
  { eapply loop with (T := cw_tp fn) (tpl := cw_tpl fn) (tslack := cw_slack fn) (AP := bv_unsigned s4 + 8)
                     (n := Datatypes.S (length (cw_tpl fn))) (ws := ws) (W := W) (arr := arr) (lp := lp)
                     (x16 := x16) (x24 := x24) (x32 := x32) (x40 := x40) (can := can) (m0 := m0) (lo := lo) (S := S)
                     (k := 0%nat) (a := 0) (gp := gp) (tp := tp) (s4 := s4) (s9 := s9) (F := F) (r := r) (nargs := nargs).
    all: first [ eassumption
               | reflexivity
               | apply cw_tpl_ro; exact HFN
               | apply notin_nul_lit; exact F1
               | exact (conj HL1 (conj HL2 HL3))
               | (split; lia)
               | lia
               | (unfold cw_inv; refine (conj MI (conj MU (conj WM (conj ST (ex_intro _ jb BUF))))))
               | idtac ].
    unfold items_pre. intros j i Hj Hjn. change (skipn 0 (cw_tpl fn)) with (cw_tpl fn) in Hj.
    rewrite (cw_tpl_items fn HFN) in Hj.
    split.
    - rewrite forallb_forall in F4. specialize (F4 i (nth_error_In _ _ Hj)).
      destruct i; cbn in F4 |- *; first [exact I | apply Z.leb_le; exact F4].
    - intros y Hy. replace (bv_unsigned s4 + 8 + 8 * (0 + Z.of_nat j)) with (bv_unsigned s4 + 8 + 8 * Z.of_nat j) by lia.
      eapply HARGS; [lia | rewrite Nat2Z.id; exact Hj | exact Hy]. }
  intros ms' (k & a & yra & yt0 & yt1 & yt2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & ys6 & ys7 & ys11 & yt3 &
              yt4 & yt5 & yt6 & Fc' & fc' & m' & E & HI' & FRM' & FP').
  subst ms'. destruct HI' as (MI' & MU' & WM' & ST' & jb' & BUF').
  unfold cw_items_post. do 28 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact ST'|]. split; [exact BUF'|].
  split; [exact FRM' | exact FP'].
Qed.
