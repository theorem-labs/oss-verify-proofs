(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0ArtCellsK_b Ba0BssZeroK_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanNodesLibEK AsanNodesMmLibK HandoffLazyK.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx As0Tables ArtMem ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b BatRzLog_b BatAllocA_b BatCls_b BatDepotA_b BatDepot_b.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatInv_b BatFsInv_b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition I_KSPACE : nat := 5.   Definition I_PARR : nat := 6.   Definition I_THREAD : nat := 7.   Definition I_CTX : nat := 8.
Definition I_FAKE : nat := 11.    Definition I_L2 : nat := 14.    Definition I_BLK : nat := 15.   Definition I_DTLS : nat := 10.   (* [comment removed for export] *)

Definition e_at (k : list kentry) (b : expr) (off : Z) (w : nat) : expr :=
  match kfind_word k b off w with Some e => e | None => ELit 0 end.
Definition bT (cs : acs) : expr := am_base (role cs I_THREAD).
Definition bC (cs : acs) : expr := am_base (role cs I_CTX).
Definition bF (cs : acs) : expr := am_base (role cs I_FAKE).
Definition bP (cs : acs) : expr := am_base (role cs I_PARR).
Definition bL2 (cs : acs) : expr := am_base (role cs I_L2).
Definition bBLK (cs : acs) : expr := am_base (role cs I_BLK).
Definition bD (cs : acs) : expr := am_base (role cs I_DTLS).
(* [comment removed for export] *)
Definition spbE (cs : acs) : expr := e_at (kn cs) (ELit 0) (1295832 + 32) 8.
Definition bK (cs : acs) : expr := fst (split_lit (spbE cs)).
(* [comment removed for export] *)
Definition topE (cs : acs) : expr := e_at (kn cs) (bT cs) 8 8.
Definition botE (cs : acs) : expr := e_at (kn cs) (bT cs) 16 8.
(* [comment removed for export] *)
Definition tfE (cs : acs) : expr := e_at (kn cs) (ELit 0) 0x211b08 8.
Definition stE (cs : acs) : expr := e_at (kn cs) (ELit 0) (0x211b08 + 24) 4.

Definition TP : Z := 0x673d00.
Definition TSD : Z := 0x6951b8.
Definition LOFF : Z := 0x10.

Definition as0_ar (E : env) (cs : acs) : asan_run :=
  AR (uE E e_sp0) (uE E (topE cs)) (uE E (botE cs)) (rbase E cs I_FAKE) (uE E (bK cs) + 0x10000).
Definition as0_rn (E : env) (cs : acs) : art_run :=
  ARN (as0_ar E cs) (rbase E cs I_THREAD) (rbase E cs I_CTX) TP 0 TSD LOFF ((uE E (bK cs) + 0x10000) / 65536)
      (rbase E cs I_KSPACE) (rbase E cs I_PARR) (rbase E cs I_L2) (rbase E cs I_BLK) (rbase E cs I_DTLS).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_var_in (k : list kentry) (e : expr) (lo hi : Z) : bool :=
  match e with EVar _ => existsb (kentry_eqb (KRange e lo hi)) k | _ => false end.

(* [comment removed for export] *)
Definition B1 : Z := 5867644.
Definition B2 : Z := 2376368.
Definition img_cover (k : list kentry) (lo hi : Z) : bool :=
  existsb (fun K => match K with KImg l h => (Z.leb l lo && Z.leb hi h)%bool | _ => false end) k.
Definition xlo_pos (k : list kentry) (e : expr) : bool := match xlo k e with Some lo => Z.ltb 0 lo | None => false end.
Definition lit_len (cs : acs) (i : nat) (L : Z) : bool := expr_eqb (am_len (role cs i)) (ELit L).
Definition vis_in (cs : acs) (b n : expr) : bool := existsb (fun p => (expr_eqb (fst p) b && expr_eqb (snd p) n)%bool) (a_vis cs).

(* [comment removed for export] *)
Definition glob_chk (k : list kentry) (g : Z * Z) : bool :=
  ((Z.eqb (snd g / 8) 0 || chk_zero k (ELit 0) (fst g / 8 + 0x7fff8000) (snd g / 8)) && (if Z.eqb (snd g mod 8) 0 then true else chk_word k (ELit 0) (fst g / 8 + 0x7fff8000 + snd g / 8) 1 (ELit (snd g mod 8)))
   && (0x10000 <=? fst g) && (fst g <? 0x696000) && (0 <=? snd g) && (snd g <? 4096))%bool.

Definition art_sym_list (cs : acs) : list bool :=
  let k := kn cs in
  [ ((17 =? Z.of_nat (length (a_maps cs))));
    (chk_word k (ELit 0) (1295832 + 32) 8 (spbE cs));
    (Z.eqb (snd (split_lit (spbE cs))) 0x10000);
    (chk_word k (ELit 0) (1295832 + 48) 8 (eaddz (spbE cs) (2 ^ 37)));
    (chk_word k (ELit 0) (1295832 + 64 + 8) 8 (bP cs));
    (chk_word k (ELit 0) TSD 8 (bC cs));
    (chk_word k (bC cs) 152 8 (bT cs));
    (chk_word k (bT cs) 0 8 (bC cs));
    (chk_word k (bC cs) 8 4 (ELit 0));
    (chk_word k (bT cs) 8 8 (topE cs));
    (chk_word k (bT cs) 16 8 (botE cs));
    (chk_word k (bT cs) 40 1 (ELit 0));
    (chk_word k (bT cs) 3168 1 (ELit 0));
    (chk_wr k (bT cs) 0 4096);
    (chk_zero k (bT cs) 80 3088);
    (chk_zero k (bK cs) 0x2000010000 4096);
    (chk_wr k (bK cs) 0x2000010000 4096);
    (chk_wr k (bF cs) 0 0xb09000);
    (chk_word k (ELit 0) TP 8 (bF cs));
    (chk_word k (bT cs) 72 8 (bF cs));
    (chk_word k (bF cs) 88 8 (ELit 20));
    (chk_zero k (bF cs) 0 88);
    (chk_zero k (bF cs) 96 (4096 + 32768 - 96));
    (chk_word k (ELit 0) 0x621b28 8 (bL2 cs));
    (chk_word k (ELit 0) (0x211b08 + 16) 8 (bBLK cs));
    (chk_word k (ELit 0) 0x211b08 8 (tfE cs));
    (is_var_in k (tfE cs) 2 3);
    (chk_word k (ELit 0) (0x211b08 + 24) 4 (stE cs));
    (is_var_in k (stE cs) 2 3);
    (chk_wr k (ELit 0) 0x221b18 4194308);
    (chk_wr k (ELit 0) 0x211b08 32);
    (chk_wr k (bL2 cs) 0 (2 ^ 20));
    (chk_wr k (bBLK cs) 0 (2 ^ 23));
    (chk_word k (bL2 cs) 24 4 (ELit 0));
    (chk_word k (bL2 cs) 16 8 (e_at k (bL2 cs) 16 8));
    (chk_word k (ELit 0) B1 4 (e_at k (ELit 0) B1 4));
    (is_var_in k (e_at k (ELit 0) B1 4) 0 1);
    (chk_word k (ELit 0) B2 4 (e_at k (ELit 0) B2 4));
    (is_var_in k (e_at k (ELit 0) B2 4) 0 1);
    (img_cover k DEP_LO B2);
    (img_cover k (B2 + 4) B1);
    (img_cover k (B1 + 4) DEP_HI);
    (amap_eqb (role cs 0) M_LOW);
    (amap_eqb (role cs 1) M_GAP);
    (amap_eqb (role cs 2) M_HIGH);
    (xlo_pos k (bT cs));
    (xlo_pos k (bC cs));
    (xlo_pos k (bF cs));
    (lit_len cs I_KSPACE 0x2000011000);
    (lit_len cs I_PARR 0x800000);
    (lit_len cs I_THREAD 4096);
    (lit_len cs I_CTX 0x10000);
    (lit_len cs I_FAKE 0xb09000);
    (lit_len cs I_L2 0x100000);
    (lit_len cs I_BLK 0x800000);
    (* [comment removed for export] *)
    (lit_len cs I_DTLS 4096); (xlo_pos k (bD cs)); (chk_word k (ELit 0) (1295832 + 64 + 16) 8 (bP cs)); (vis_in cs (ELit 0x10000) (ELit 0x686000));
    (vis_in cs (bF cs) (ELit 0xb09000));
    (vis_in cs e_top e_stk_len);
    (* [comment removed for export] *)
    (img_cover k 0x131000 0x139000);
    (* [comment removed for export] *)
    (chk_word k (ELit 0) (TP + 8) 8 (bD cs)); (chk_word k (bD cs) 24 8 (ELit TP));
    (chk_zero k (ELit 0) 2147459072 9784); (chk_zero k (ELit 0) 2147468860 8); (chk_zero k (ELit 0) 2147468884 12); (chk_zero k (ELit 0) 2147469040 32); (chk_zero k (ELit 0) 2147469104 143560); (chk_zero k (ELit 0) 2147612848 701264);
    (forallb (glob_chk k) ART_GLOBALS) ]%bool.
Definition art_sym_chk (cs : acs) : bool := forallb (fun b => b) (art_sym_list cs).

Fixpoint all_true (l : list bool) : Prop := match l with [] => True | b :: r => b = true /\ all_true r end.
Lemma all_true_of : forall l, forallb (fun b => b) l = true -> all_true l.
Proof. induction l as [|b l IH]; intros H; [exact I|]. cbn [forallb] in H. apply andb_prop in H as [H1 H2]. split; [exact H1 | exact (IH H2)]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bKS (cs : acs) : expr := am_base (role cs I_KSPACE).
(* [comment removed for export] *)
Definition E_RISX (cs : acs) : expr := EAlu Instr.ALU_ADD (bK cs) (ELit 0x2000010000).

Fixpoint hsplit (r : expr) (h : list hop) : option (list hop * list hop) :=
  match h with
  | [] => None
  | HSub b n :: t =>
      if (expr_eqb b r && expr_eqb n (ELit 4096))%bool then Some ([], t)
      else match hsplit r t with Some (h1, h2) => Some (HSub b n :: h1, h2) | None => None end
  | x :: t => match hsplit r t with Some (h1, h2) => Some (x :: h1, h2) | None => None end
  end.
Lemma hsplit_eq : forall r h h1 h2, hsplit r h = Some (h1, h2) -> h = h1 ++ HSub r (ELit 4096) :: h2.
Proof.
  intros r h. induction h as [|x t IH]; intros h1 h2 H; [discriminate|]. cbn [hsplit] in H.
  destruct x as [b n|b n].
  - destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
  - destruct (expr_eqb b r && expr_eqb n (ELit 4096))%bool eqn:Hb.
    + injection H as <- <-. apply andb_prop in Hb as [B1 B2]. apply expr_eqb_eq in B1. apply expr_eqb_eq in B2. subst. reflexivity.
    + destruct (hsplit r t) as [[a1 a2]|] eqn:Hs; [|discriminate]. injection H as <- <-. cbn [app]. f_equal. apply IH. reflexivity.
Qed.

Definition is_rng (b n : expr) (b0 : expr) (L : Z) : bool := (expr_eqb b b0 && expr_eqb n (ELit L))%bool.
(* [comment removed for export] *)
Definition hop_pre (cs : acs) (x : hop) : bool :=
  match x with HSub _ _ => true | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000)%bool end.
(* [comment removed for export] *)
Definition hop_zone (cs : acs) (x : hop) : bool :=
  match x with
  | HSub _ _ => true
  | HCons b n => (is_rng b n (bBLK cs) 0x800000 || is_rng b n (bP cs) 0x800000 || is_rng b n (bKS cs) 0x2000011000
                  || is_rng b n (ELit 0x7fff7000) 0x10000000 || is_rng b n (ELit 0x8fff7000) 0x20000000000 || is_rng b n (ELit 0x2008fff7000) 0xdfff0001000)%bool
  end.
(* [comment removed for export] *)
Definition vis_hi (k : list kentry) (p : expr * expr) : bool :=
  ((expr_eqb (fst p) e_top && expr_eqb (snd p) e_stk_len)
   || match xhi k (fst p), snd p with Some hi, ELit n => (0 <=? n) && (n <? 2 ^ 64) && (hi + n <=? 2 ^ 47) | _, _ => false end)%bool.
(* [comment removed for export] *)
Definition apx (k : list kentry) (zb : expr) (zn : Z) (p : expr * expr) : bool :=
  let '(zb', zk) := split_lit zb in let '(pb, pk) := split_lit (fst p) in
  (flat_x k zb' zk (ELit zn) && flat_x k pb pk (snd p) && ranges_apart_x k zb' zk (ELit zn) pb pk (snd p))%bool.
(* [comment removed for export] *)
Definition own_ok (cs : acs) (p : expr * expr) : bool :=
  let k := kn cs in
  (is_rng (fst p) (snd p) (bBLK cs) 0x800000
   || is_rng (fst p) (snd p) (E_RISX cs) 4096
   || (apx k (bKS cs) 0x2000011000 p && apx k (bP cs) 0x800000 p
       && (apx k (bBLK cs) 0x800000 p || (expr_eqb (snd p) (ELit 4096) && (12 <=? ealign k (fst p))))))%bool.
Definition art_lazy_chk (cs : acs) : bool :=
  (match hsplit (E_RISX cs) (a_hlz cs) with Some (h1, _) => forallb (hop_pre cs) h1 | None => false end
   && forallb (hop_zone cs) (a_hlz cs)
   && forallb (fun p => vis_hi (kn cs) p && own_ok cs p) (a_vis cs ++ a_ghost cs)
   && (12 <=? ealign (kn cs) (bBLK cs)) && vis_in cs (bBLK cs) (ELit 0x800000))%bool.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma uE_lit : forall E z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z.
Proof. intros E z Hz. unfold uE. cbn [edenot]. apply u64_lit. exact Hz. Qed.

Lemma class_size_pos : forall c, 1 <= c <= 30 -> 0 < AsanTab.class_size c.
Proof.
  intros c Hc. assert (H : forallb (fun c => 0 <? AsanTab.class_size c) (AsanTab.zrange 1 30) = true) by (vm_compute; reflexivity).
  apply Z.ltb_lt. apply (proj1 (forallb_forall _ _) H). unfold AsanTab.zrange. apply AsanTab.in_ziota. change (Z.of_nat (Z.to_nat 30)) with 30. lia.
Qed.

Section Derive.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.

  Variable cs : acs.
  Hypothesis CHK0 : as0_chk cs = true.
  Hypothesis CHKL : art_lits_chk cs = true.
  Hypothesis CHKS : art_sym_chk cs = true.

  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  #[local] Notation rn := (as0_rn E cs).
  #[local] Notation T := (rbase E cs I_THREAD).
  #[local] Notation CTX := (rbase E cs I_CTX).
  #[local] Notation KB := (rbase E cs I_KSPACE).
  #[local] Notation SPB := (uE E (bK cs) + 0x10000).
  #[local] Notation SP0 := (uE E e_sp0).

  (* [comment removed for export] *)
  Hypothesis HGEO_SPB : KB < SPB <= KB + 65536 /\ SPB mod 65536 = 0.
  Hypothesis HGEO_STK : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
                        /\ SP0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= SP0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.

  (* [comment removed for export] *)
  Hypothesis HSP16 : SP0 + 16 <= 2 ^ 47.
  Hypothesis HSPA : SP0 mod 16 = 0.                                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac chk_split H := repeat (let X := fresh "C" in apply andb_prop in H as [H X]).

  #[using="CHK0"] Lemma nofog : no_fog (a_maps cs) = true.
  Proof. pose proof CHK0 as H. unfold as0_chk in H. chk_split H. exact H. Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma cellW : forall b off w v, chk_word (kn cs) b off w v = true -> cellA FULL (uE E b + off) w (uE E v).
  Proof.
    intros b off w v H. unfold cell.
    exact (proj2 (hc_word ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off w v HC H)).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellL : forall a w v, In (a, w, v) ART_LITW -> cellA FULL a w v.
  Proof. exact (art_lit sp brk0 rdraw argv envp uid hw fs Hsp Hva E cs R FULL model HC CHKL). Qed.
  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma cellLb : forall a w v,
    existsb (fun c => (Z.eqb (fst (fst c)) a && Nat.eqb (snd (fst c)) w && Z.eqb (snd c) v)%bool) ART_LITW = true -> cellA FULL a w v.
  Proof.
    intros a w v H. apply existsb_exists in H as ([[a' w'] v'] & Hin & Hb). cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
    exact (cellL _ _ _ Hin).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma cellZ : forall b off n a (w : nat), chk_zero (kn cs) b off n = true -> (w <= 8)%nat ->
    uE E b + off <= a -> a + Z.of_nat w <= uE E b + off + n -> cellA FULL a w 0.
  Proof.
    intros b off n a w H Hw H1 H2. unfold cell.
    exact (hc_zero_cell ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H a w Hw H1 H2).
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH R model HC"] Lemma wrK : forall b off n, chk_wr (kn cs) b off n = true -> wrA FULL (uE E b + off) n.
  Proof.
    intros b off n H d k Hd Hk.
    exact (hc_wr ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH E cs R FULL model b off n HC H d k Hd Hk).
  Qed.

  #[using="CHKS E"] Lemma len17 : length (a_maps cs) = 17%nat.
  Proof. pose proof (all_true_of _ CHKS) as H. cbn [all_true art_sym_list] in H. destruct H as [H _]. apply Z.eqb_eq in H. lia. Qed.

  #[using="CHKS"] Lemma sym_all : all_true (art_sym_list cs).
  Proof. exact (all_true_of _ CHKS). Qed.
  Ltac chk_old := let H := fresh in pose proof sym_all as H; cbn [all_true art_sym_list] in H; decompose [and] H; assumption.
  (* [comment removed for export] *)
  Ltac chk_find eqt g l i :=
    lazymatch l with
    | cons ?hd ?tl =>
        first [ (eqt hd g;
                 exact (proj1 (List.Forall_nth (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
                          (proj2 (List.Forall_forall (fun xb : bool => (fun yb : bool => yb) xb = true) (art_sym_list cs))
                             (proj1 (List.forallb_forall (fun yb : bool => yb) (art_sym_list cs)) CHKS))
                          i true (proj1 (Nat.ltb_lt i (length (art_sym_list cs))) (@eq_refl bool true))))
              | chk_find eqt g tl constr:(Datatypes.S i) ]
    end.
  Ltac chk :=
    first [ lazymatch goal with
            | |- ?g = true =>
                let l := eval cbv beta zeta delta [art_sym_list] in (art_sym_list cs) in
                first [ chk_find ltac:(fun u v => constr_eq u v) g l constr:(Datatypes.O) | chk_find ltac:(fun u v => unify u v) g l constr:(Datatypes.O) ]
            end
          | chk_old ].

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs cs R FULL model HC HSP16"] Lemma sp0_win : 0x7fff80000000 <= SP0 <= 2 ^ 47.
  Proof. destruct (co_isp _ _ _ _ _ _ _ _ _ _ _ HC) as (_ & W & _). unfold sp_window_lo, sp_window_hi in W. unfold uE in *. lia. Qed.

  #[using="CHKS"] Lemma role_shadow : rbase E cs 0 = 0x7fff7000 /\ rlen E cs 0 = 0x10000000 /\ rbase E cs 1 = 0x8fff7000 /\ rlen E cs 1 = 0x20000000000
                      /\ rbase E cs 2 = 0x2008fff7000 /\ rlen E cs 2 = 0xdfff0001000.
  Proof.
    assert (H0 : amap_eqb (role cs 0) M_LOW = true) by chk. assert (H1 : amap_eqb (role cs 1) M_GAP = true) by chk.
    assert (H2 : amap_eqb (role cs 2) M_HIGH = true) by chk.
    apply amap_eqb_eq in H0. apply amap_eqb_eq in H1. apply amap_eqb_eq in H2. unfold rbase, rlen. rewrite H0, H1, H2.
    cbn [M_LOW M_GAP M_HIGH am_base am_len]. rewrite !uE_lit by lia. repeat split; reflexivity.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608
    /\ (rbase E cs i + L <= 0x10000 \/ 0x696000 <= rbase E cs i)
    /\ ((3 <= i)%nat -> rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i).
  Proof.
    intros i L Hi HL HLr. unfold lit_len in HL. apply expr_eqb_eq in HL.
    pose proof (role_lit E cs i L HL HLr) as El.
    destruct (role_geo ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i HC nofog ltac:(rewrite len17; exact Hi)) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    rewrite El in *. cbn [img_lo img_hi ASAN0] in G4.
    repeat split; try assumption. intros H3.
    destruct role_shadow as (S0 & L0 & S1 & L1 & S2 & L2).
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 0 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A0.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 1 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A1.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i 2 HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; lia) ltac:(lia)) as A2.
    rewrite El, ?S0, ?L0, ?S1, ?L1, ?S2, ?L2 in *. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra : forall i j Li Lj, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 ->
    rbase E cs i + Li <= rbase E cs j \/ rbase E cs j + Lj <= rbase E cs i.
  Proof.
    intros i j Li Lj Hi Hj Hne HLi HLj Ri Rj. unfold lit_len in *. apply expr_eqb_eq in HLi. apply expr_eqb_eq in HLj.
    pose proof (role_apart ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model i j HC nofog ltac:(rewrite len17; exact Hi) ltac:(rewrite len17; exact Hj) Hne) as D.
    rewrite (role_lit E cs i Li HLi Ri), (role_lit E cs j Lj HLj Rj) in D. exact D.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma xpos : forall e, xlo_pos (kn cs) e = true -> 0 < uE E e.
  Proof.
    intros e H. unfold xlo_pos in H. destruct (xlo (kn cs) e) as [lo|] eqn:Hx; [|discriminate]. apply Z.ltb_lt in H.
    pose proof (xlo_sound ASEGS0 E _ (kn cs) e lo (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx). unfold uE. lia.
  Qed.

  Ltac lenok := first [assert_succeeds (idtac); (chk)].
  Ltac RG i L := let X := fresh "G" in pose proof (rg i L ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(lia)) as X.
  Ltac RA i j Li Lj := let X := fresh "D" in
    pose proof (ra i j Li Lj ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia)
                  ltac:(unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK; lia) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as X.

  #[using="HGEO_SPB"] Lemma spb_qs : 65536 * (SPB / 65536) = SPB.
  Proof. destruct HGEO_SPB as (_ & Hm). pose proof (Z.div_mod SPB 65536 ltac:(lia)). lia. Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rgl : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i mod 4096 = 0 /\ 0 <= rbase E cs i /\ 0 < L /\ rbase E cs i + L <= SP0 - 8388608.
  Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (G1 & G2 & G3 & G4 & _). auto. Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_img : forall i L, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x10000 \/ 0x696000 <= rbase E cs i.
  Proof. intros i L Hi HL HLr. destruct (rg i L Hi HL HLr) as (_ & _ & _ & _ & G5 & _). exact G5. Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_STK"] Lemma rg_hole : forall i L, (3 <= i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i + L <= 0x7fff7000 \/ 0x10007fff8000 <= rbase E cs i.
  Proof. intros i L Hi HL HLr. destruct (rg i L ltac:(lia) HL HLr) as (_ & _ & _ & _ & _ & G6). apply G6. lia. Qed.
  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC"] Lemma ra_sub : forall i j Li Lj a n b m, (i < 17)%nat -> (j < 17)%nat -> i <> j -> lit_len cs i Li = true -> lit_len cs j Lj = true ->
    0 <= Li < 2 ^ 64 -> 0 <= Lj < 2 ^ 64 -> rbase E cs i <= a -> a + n <= rbase E cs i + Li -> rbase E cs j <= b -> b + m <= rbase E cs j + Lj ->
    apart a n b m.
  Proof.
    intros i j Li Lj a n b m Hi Hj Hne HLi HLj Ri Rj Ha Hn Hb Hm. unfold apart.
    destruct (ra i j Li Lj Hi Hj Hne HLi HLj Ri Rj) as [X|X]; [left | right]; lia.
  Qed.
  Ltac IDX := unfold I_KSPACE, I_PARR, I_THREAD, I_CTX, I_FAKE, I_L2, I_BLK, I_DTLS; lia.
  Ltac RASUB i j Li Lj := apply (ra_sub i j Li Lj); [IDX | IDX | IDX | chk | chk | lia | lia | lia | lia | lia | lia].

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_run_ok : art_run_ok rn.
  Proof.
    pose proof sp0_win as W. pose proof spb_qs as Q. destruct HGEO_SPB as ((K1 & K2) & K3).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
    pose proof (rgl I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (t1 & t2 & t3 & t4).
    pose proof (rgl I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (c1 & c2 & c3 & c4).
    pose proof (rgl I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (l1 & l2 & l3 & l4).
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    pose proof (rgl I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (f1 & f2 & f3 & f4).
    pose proof (xpos (bT cs) ltac:(chk)) as PT. pose proof (xpos (bC cs) ltac:(chk)) as PC. pose proof (xpos (bF cs) ltac:(chk)) as PF.
    change (uE E (bT cs)) with T in PT. change (uE E (bC cs)) with CTX in PC. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
    assert (QT : exists qt, T = 4096 * qt) by (exists (T / 4096); pose proof (Z.div_mod T 4096 ltac:(lia)); lia).
    assert (T4 : 4096 <= T) by (destruct QT as [qt Eq]; lia).
    assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
    assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
    assert (KHOLE : 0x10007fff8000 <= KB).
    { destruct (rg_hole I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia. }
    unfold art_run_ok, art_geo, rn_HI, rn_spb, rn_ris, rn_spb, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES.
    cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_tp rn_key rn_tsd rn_loff rn_qs rn_kbase rn_parr rn_l2 rn_blk ar_sptop ar_space_beg ar_fs]. unfold TP, TSD, LOFF.
    rewrite Q. change (2 ^ 20) with 0x100000. change (2 ^ 23) with 0x800000.
    (* [comment removed for export] *)
    split.
    { split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact T4|]. split; [lia|]. split; [exact (rg_img I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
      split; [exact (rg_hole I_THREAD 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
      split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [exact QT|].
      split; [exact C4|]. split; [lia|].
      split; [destruct (rg_img I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
      split; [destruct (rg_hole I_CTX 0x10000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
      split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
      split; [RASUB I_THREAD I_CTX 4096 0x10000|]. lia. }
    split; [reflexivity|]. split; [exact g1|]. split; [lia|]. split; [lia|].
    split; [exact p1|].
    split; [destruct (rg_img I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|]. split; [lia|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    (* [comment removed for export] *)
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [RASUB I_L2 I_THREAD 0x100000 4096|]. split; [RASUB I_L2 I_CTX 0x100000 0x10000|]. split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|].
    split; [unfold apart; destruct (rg_hole I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
    split; [RASUB I_BLK I_THREAD 0x800000 4096|]. split; [RASUB I_BLK I_CTX 0x800000 0x10000|]. split; [RASUB I_BLK I_KSPACE 0x800000 0x2000011000|].
    split; [unfold apart; destruct (rg_hole I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; [left | right]; lia|].
    split; [RASUB I_PARR I_THREAD 0x800000 4096|]. split; [RASUB I_PARR I_CTX 0x800000 0x10000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
    split; [RASUB I_PARR I_L2 0x800000 0x100000|]. split; [RASUB I_PARR I_BLK 0x800000 0x800000|].
    split; [RASUB I_FAKE I_THREAD 0xb09000 4096|]. split; [RASUB I_FAKE I_CTX 0xb09000 0x10000|]. split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
    split; [RASUB I_FAKE I_L2 0xb09000 0x100000|]. split; [RASUB I_FAKE I_BLK 0xb09000 0x800000|]. split; [RASUB I_FAKE I_PARR 0xb09000 0x800000|].
    split; [lia|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [exact (rg_img I_FAKE 0xb09000 ltac:(IDX) ltac:(chk) ltac:(lia))|]. split; [exact F4|].
    (* [comment removed for export] *)
    pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
    pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
    assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
    cbn [as0_rn rn_dtls].
    split; [destruct (rg_img I_L2 0x100000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
    split; [destruct (rg_img I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as [X|X]; lia|].
    split; [RASUB I_FAKE I_KSPACE 0xb09000 0x2000011000|].
    split; [exact D4|]. split; [lia|].
    split; [exact (rg_img I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [split; [lia|]; split; [|lia]; exact (rg_hole I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia))|].
    split; [RASUB I_DTLS I_THREAD 4096 4096|]. split; [RASUB I_DTLS I_CTX 4096 0x10000|]. split; [RASUB I_DTLS I_KSPACE 4096 0x2000011000|].
    split; [RASUB I_DTLS I_PARR 4096 0x800000|]. split; [RASUB I_DTLS I_L2 4096 0x100000|]. split; [RASUB I_DTLS I_BLK 4096 0x800000|].
    split; [RASUB I_DTLS I_FAKE 4096 0xb09000|].
    (* [comment removed for export] *)
    split; [RASUB I_THREAD I_KSPACE 4096 0x2000011000|]. split; [RASUB I_CTX I_KSPACE 0x10000 0x2000011000|].
    split; [RASUB I_L2 I_KSPACE 0x100000 0x2000011000|]. split; [RASUB I_PARR I_KSPACE 0x800000 0x2000011000|].
    exact KHOLE.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma spb_val : uE E (spbE cs) = SPB.
  Proof.
    assert (Hs : Z.eqb (snd (split_lit (spbE cs))) 0x10000 = true) by chk. apply Z.eqb_eq in Hs.
    pose proof (split_lit_denot E (spbE cs) (bK cs) 0x10000) as Hd. unfold bK in Hd |- *.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold bK in K1, K2.
    destruct (split_lit (spbE cs)) as [b k] eqn:Hspl. cbn [fst snd] in *. subst k. specialize (Hd eq_refl).
    unfold uE in *. rewrite Hd. apply u64_lit. lia.
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16"] Lemma ris_val : uE E (eaddz (spbE cs) (2 ^ 37)) = SPB + 2 ^ 37.
  Proof.
    unfold eaddz, uE. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. fold (uE E (spbE cs)). rewrite spb_val.
    apply Z.mod_small. pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _). RG I_KSPACE 0x2000011000. unfold uE in *. lia.
  Qed.
  #[using="cs"] Lemma uE0 : uE E (ELit 0) = 0.
  Proof. apply uE_lit. lia. Qed.

  Ltac CL := apply cellLb; vm_compute; reflexivity.
  Ltac CW a w v := let X := fresh in pose proof (cellW (ELit 0) a w v ltac:(chk)) as X; rewrite uE0 in X; rewrite ?Z.add_0_l in X.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH cs CHKS E R model HC"] Lemma got_none : forall a, 0x131000 <= a < 0x139000 -> FULL (Z_to_bv 64 a) = None.
  Proof.
    intros a Ha. assert (H : img_cover (kn cs) 0x131000 0x139000 = true) by chk.
    unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
    unfold in_hull. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_rt_statics : art_rt_statics rn FULL.
  Proof.
    unfold art_rt_statics, art_rt_tlsgot, art_prim_consts, art_layout, art_tsd, art_alloc_rodata, art_rz_rodata, DRoD, rn_spb, rn_ris, rn_spb, SB, kHighMemEnd.
    cbn [as0_rn rn_qs rn_tp rn_key rn_tsd rn_ctx rn_t rn_loff]. unfold TP, TSD, LOFF. rewrite spb_qs.
    pose proof (cellW (ELit 0) (1295832 + 32) 8 (spbE cs) ltac:(chk)) as X1. rewrite uE0, spb_val in X1.
    pose proof (cellW (ELit 0) (1295832 + 48) 8 (eaddz (spbE cs) (2 ^ 37)) ltac:(chk)) as X2. rewrite uE0, ris_val in X2.
    pose proof (cellW (ELit 0) TSD 8 (bC cs) ltac:(chk)) as X3. rewrite uE0 in X3. unfold TSD in X3.
    pose proof (cellW (bC cs) 152 8 (bT cs) ltac:(chk)) as X4.
    change (uE E (bC cs)) with CTX in *. change (uE E (bT cs)) with T in *.
    RG I_THREAD 4096. RG I_CTX 0x10000. pose proof sp0_win.
    pose proof (xpos (bC cs) ltac:(chk)) as PC. change (uE E (bC cs)) with CTX in PC.
    assert (C4 : 4096 <= CTX) by (pose proof (Z.div_mod CTX 4096 ltac:(lia)); lia).
    repeat match goal with |- _ /\ _ => split end; try exact X1; try exact X2; try exact X3; try exact X4; try exact got_none; try CL; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_thread : art_rt_thread rn FULL.
  Proof.
    unfold art_rt_thread. cbn [as0_rn as0_ar rn_t rn_ctx rn_tp rn_loff rn_ar ar_stack_top ar_stack_bottom]. unfold TP, LOFF.
    pose proof (wrK (bT cs) 0 4096 ltac:(chk)) as W. rewrite Z.add_0_r in W.
    pose proof (cellW (bT cs) 0 8 (bC cs) ltac:(chk)) as X1. rewrite Z.add_0_r in X1.
    pose proof (cellW (bC cs) 8 4 (ELit 0) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (bT cs) 8 8 (topE cs) ltac:(chk)) as X3. pose proof (cellW (bT cs) 16 8 (botE cs) ltac:(chk)) as X4.
    pose proof (cellW (bT cs) 40 1 (ELit 0) ltac:(chk)) as X5. rewrite uE0 in X5.
    pose proof (cellW (bT cs) 3168 1 (ELit 0) ltac:(chk)) as X6. rewrite uE0 in X6.
    repeat match goal with |- _ /\ _ => split end; try assumption. CL.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Lemma kshadow_wr : wrA FULL (0x7fff8000 + 8192 * (SPB / 65536)) (2 ^ 34).
  Proof.
    destruct (as0_chk_parts cs CHK0) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3). RG I_KSPACE 0x2000011000.
    destruct G as (g1 & g2 & g3 & g4 & g5 & g6). specialize (g6 ltac:(unfold I_KSPACE; lia)).
    pose proof (Z.div_mod SPB 65536 ltac:(lia)) as DM. rewrite K3 in DM.
    set (q := SPB / 65536) in *.
    apply art_wr_of_defined; [lia | lia |].
    intros x Hx.
    apply (hl_shadow_defined ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok AH asan0_shadow_ok ltac:(cbn; unfold SHB_LO; lia)
             E cs R FULL model HC C1 C4 C5 M_HIGH 0x2008fff7000 0xdfff0001000 C8 eq_refl eq_refl eq_refl); unfold SHB_LO, SHB_LEN; lia.
  Qed.

  #[using="cs E"] Lemma wr0 : forall a, wrA FULL a 0.
  Proof. intros a d k Hd Hk. assert (k = 0%nat) by lia. subst k. reflexivity. Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_rt_primary : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_primary FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_primary. cbn [art_gs0 g_inited g_cls as0_rn rn_t rn_qs]. unfold rn_spb, rn_ris, rn_spb. cbn [as0_rn rn_qs]. rewrite spb_qs.
    assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
    assert (ZR : chk_zero (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    assert (WR : chk_wr (kn cs) (bK cs) 0x2000010000 4096 = true) by chk.
    split; [|split; [|exact kshadow_wr]].
    - intros c Hc. split; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
    - intros c Hc. split; [|split; [|split; [|split]]].
      + unfold art_cls_rep, art_cache_rep, art_region_rep, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length]. change (Z.of_nat 0) with 0.
        pose proof (wrK (bK cs) 0x2000010000 4096 WR) as W.
        repeat match goal with |- _ /\ _ => split end;
          try (apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia);
          try (apply (cellZ (bK cs) 0x2000010000 4096 _ _ ZR); lia);
          try (intros j Hj; cbn in Hj; lia); try apply wr0.
        apply (wr_sub _ _ _ _ _ _ W); lia.
      + unfold art_cls_ok, art_cls0. cbn [cl_cache cl_free cl_mfa cl_au cl_mu cl_na cl_nfr length app]. pose proof (class_size_pos c Hc).
        repeat match goal with |- _ /\ _ => split end; try lia; try (exists 0; lia); try constructor.
      + unfold art_cls0. cbn [cl_cache]. intros H. congruence.
      + exists 0. reflexivity.
      + unfold art_cls0. cbn [cl_au]. intros H. lia.          (* [comment removed for export] *)
  Qed.

  #[using="Type"] Theorem as0_art_rt_chunks : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_chunks FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_chunks. cbn [art_gs0 g_cls g_st]. unfold art_cls0. cbn [cl_cache cl_free cl_au cl_mu app].
    intros c Hc. pose proof (class_size_pos c Hc) as Hs. split; [|split; [|split]].
    - intros x Hx. lia.
    - intros w [].
    - intros w _. reflexivity.                       (* [comment removed for export] *)
    - intros w (W1 & W2 & _). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_sec : cellA FULL (1295832 + 64 + 616) 4 0.
  Proof.
    apply (cell0_cat FULL (1295832 + 64 + 616) 1 3); [lia | lia | lia | CL | CL].
  Qed.
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Lemma lock_quar : cellA FULL (0x13c8b0 + 152) 4 0.
  Proof.
    apply (cell0_cat FULL (0x13c8b0 + 152) 1 3); [lia | lia | lia | CL |].
    apply (cell0_cat FULL (0x13c8b0 + 152 + 1) 1 2); [lia | lia | lia | CL | CL].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHKL CHKS R model HC"] Theorem as0_art_rt_sec : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_sec FSG rn (art_gs0 FSG gfs0 k0) [] FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_sec. cbn [art_gs0 g_sec g_sec_committed g_log as0_rn rn_parr length]. change (Z.of_nat 0) with 0.
    pose proof (cellW (ELit 0) (1295832 + 64 + 8) 8 (bP cs) ltac:(chk)) as X. rewrite uE0 in X.
    pose proof (cellW (ELit 0) (1295832 + 64 + 16) 8 (bP cs) ltac:(chk)) as X2. rewrite uE0 in X2.     (* [comment removed for export] *)
    repeat match goal with |- _ /\ _ => split end; try exact lock_sec; try CL; try exact X; try exact X2.
    - intros H. congruence.
    - intros H. discriminate H.
    - intros i s H. destruct i; discriminate H.
    - intros p [].
    - lia.                                           (* [comment removed for export] *)
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL CHKS R model HC"] Theorem as0_art_rt_quar : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_quar FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_quar. cbn [art_gs0 g_qt g_qg as0_rn rn_t length app map art_batches_bytes fold_right]. change (Z.of_nat 0) with 0.
    assert (ZT : chk_zero (kn cs) (bT cs) 80 3088 = true) by chk.
    repeat match goal with |- _ /\ _ => split end; try lia; try exact lock_quar; try CL.
    - exists 0, 0. repeat split; try reflexivity; apply (cellZ (bT cs) 80 3088 _ _ ZT); change (uE E (bT cs)) with T; lia.
    - exists 0, 0. repeat split; try reflexivity; CL.
    - constructor.
    - intros b [].                                   (* [comment removed for export] *)
    - intros b it [].                                (* [comment removed for export] *)
    - cbn. constructor.
    - intros b [].                                   (* [comment removed for export] *)
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHKL E R model HC"] Theorem as0_art_rt_ia : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ia FSG (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. unfold art_rt_ia. cbn [art_gs0 g_ia g_qt g_qg].
    repeat match goal with |- _ /\ _ => split end; try CL.
    - intros H. discriminate H.
    - intros _. split; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC"] Lemma var_in : forall e lo hi, is_var_in (kn cs) e lo hi = true -> lo <= uE E e <= hi.
  Proof.
    intros e lo hi H. unfold is_var_in in H. destruct e; try discriminate.
    apply existsb_exists in H as (K & Hin & Heq). apply kentry_eqb_eq in Heq. subst K.
    pose proof (hb_kn ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ HC Hin) as HK. cbn [kentry_ok] in HK. unfold uE. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH E R model HC"] Lemma img_zero4 : forall lo hi a, img_cover (kn cs) lo hi = true -> lo <= a -> a + 4 <= hi -> DEP_LO <= a -> a + 4 <= DEP_HI -> cellA FULL a 4 0.
  Proof.
    intros lo hi a H H1 H2 H3 H4. unfold img_cover in H. apply existsb_exists in H as (K & Hin & Hc).
    destruct K as [| | | l h | | | | | |]; try discriminate. apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
    unfold cell.
    assert (HN : forall x : word, a <= bv_unsigned x < a + Z.of_nat 4 -> FULL x = None).
    { intros x Hx. cbn in Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      apply (hb_img ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_hull_ok AH E cs R FULL model l h HC Hin); [lia|].
      unfold in_hull, DEP_LO, DEP_HI in *. cbn [img_lo img_hi ASAN0]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    pose proof (as0_dep_rdn_zero FULL 4%nat a H3 ltac:(cbn; lia) HN) as Hz. unfold ASEGS0 in Hz. rewrite Hz.
    rewrite (wleb_zero 4 ltac:(lia)). reflexivity.
  Qed.

  Definition K0D : nat := 16384%nat.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16"] Theorem as0_art_rt_depot : forall (FSG : Type) (gfs0 : FSG), art_rt_depot FSG rn (art_gs0 FSG gfs0 K0D) FULL.
  Proof.
    intros FSG gfs0. unfold art_rt_depot, DInvD. cbn [art_gs0 g_depot as0_rn rn_l2 rn_blk]. unfold NID, STO, MAP1, DEP, apart.
    exists 1, (uE E (tfE cs)), (uE E (stE cs)).
    pose proof sp0_win as W. RG I_L2 0x100000. RG I_BLK 0x800000. RA I_L2 I_BLK 0x100000 0x800000.
    destruct G as (l1 & l2 & l3 & l4 & l5 & l6). destruct G0 as (b1 & b2 & b3 & b4 & b5 & b6).
    pose proof (var_in (tfE cs) 2 3 ltac:(chk)) as VT. pose proof (var_in (stE cs) 2 3 ltac:(chk)) as VS.
    pose proof (cellW (ELit 0) 0x211b08 8 (tfE cs) ltac:(chk)) as X1. rewrite uE0 in X1.
    pose proof (cellW (ELit 0) (0x211b08 + 24) 4 (stE cs) ltac:(chk)) as X2. rewrite uE0 in X2.
    pose proof (cellW (ELit 0) 0x621b28 8 (bL2 cs) ltac:(chk)) as X3. rewrite uE0 in X3.
    pose proof (cellW (ELit 0) (0x211b08 + 16) 8 (bBLK cs) ltac:(chk)) as X4. rewrite uE0 in X4.
    pose proof (wrK (ELit 0) 0x221b18 4194308 ltac:(chk)) as W1. rewrite uE0 in W1.
    pose proof (wrK (ELit 0) 0x211b08 32 ltac:(chk)) as W2. rewrite uE0 in W2.
    pose proof (wrK (bL2 cs) 0 (2 ^ 20) ltac:(chk)) as W3. rewrite Z.add_0_r in W3.
    pose proof (wrK (bBLK cs) 0 (2 ^ 23) ltac:(chk)) as W4. rewrite Z.add_0_r in W4.
    change (uE E (bL2 cs)) with (rbase E cs I_L2) in *. change (uE E (bBLK cs)) with (rbase E cs I_BLK) in *.
    unfold K0D. change (Z.of_nat 16384) with 16384.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia; try CL.
    - (* [comment removed for export] *)
      intros b Hb.
      pose proof (cellW (ELit 0) B1 4 (e_at (kn cs) (ELit 0) B1 4) ltac:(chk)) as Y1. rewrite uE0 in Y1. pose proof (var_in (e_at (kn cs) (ELit 0) B1 4) 0 1 ltac:(chk)) as V1.
      pose proof (cellW (ELit 0) B2 4 (e_at (kn cs) (ELit 0) B2 4) ltac:(chk)) as Y2. rewrite uE0 in Y2. pose proof (var_in (e_at (kn cs) (ELit 0) B2 4) 0 1 ltac:(chk)) as V2.
      unfold B1, B2 in *.
      destruct (Z.eq_dec b 908121) as [->|N1]; [eexists; split; [exact Y1 | lia]|].
      destruct (Z.eq_dec b 35302) as [->|N2]; [eexists; split; [exact Y2 | lia]|].
      exists 0. split; [|lia].
      destruct (Z_lt_dec b 35302); [|destruct (Z_lt_dec b 908121)].
      + apply (img_zero4 DEP_LO 2376368); [chk | unfold DEP_LO; lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (2376368 + 4) 5867644); [chk | lia | lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
      + apply (img_zero4 (5867644 + 4) DEP_HI); [chk | lia | unfold DEP_HI; lia | unfold DEP_LO; lia | unfold DEP_HI; lia].
    - (* [comment removed for export] *)
      intros id Hid. assert (id = 1) by lia. subst id.
      pose proof (cellW (bL2 cs) 16 8 (e_at (kn cs) (bL2 cs) 16 8) ltac:(chk)) as N1. pose proof (cellW (bL2 cs) 24 4 (ELit 0) ltac:(chk)) as N2. rewrite uE0 in N2.
      change (uE E (bL2 cs)) with (rbase E cs I_L2) in *.
      exists (uE E (e_at (kn cs) (bL2 cs) 16 8)), 0. pose proof (u64_range (edenot E (e_at (kn cs) (bL2 cs) 16 8))). unfold uE in *.
      repeat split; try lia; [exact N1 | replace (rbase E cs I_L2 + 16 * 1 + 8) with (rbase E cs I_L2 + 24) by ring; exact N2].
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHKL R model HC"] Theorem as0_art_rt_ghost : forall (FSG : Type) (gfs0 : FSG) (k0 : nat), art_rt_ghost FSG rn (art_gs0 FSG gfs0 k0) FULL.
  Proof.
    intros FSG gfs0 k0. assert (C : cellA FULL (0x13c8b0 + 72) 8 0xe666661) by CL.
    unfold art_rt_ghost. cbn [art_gs0 g_qt g_qg g_cls app]. split; [intros b it []|]. split; [|split; [intros b []|exact C]].
    intros c Hc. cbn [art_cls0 cl_au cl_mfa cl_cache length]. split; [intros X; exfalso; lia|]. pose proof (art_ic_mc_range c ltac:(lia)). cbn. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_SPB HGEO_STK HSP16"] Theorem as0_art_alloc_rep : forall (FSG : Type) (gfs0 : FSG), art_alloc_rep FSG rn (art_gs0 FSG gfs0 K0D) [] FULL.
  Proof.
    intros FSG gfs0. unfold art_alloc_rep.
    exact (conj as0_art_run_ok (conj as0_art_rt_statics (conj as0_art_rt_thread (conj (as0_art_rt_primary FSG gfs0 K0D)
             (conj (as0_art_rt_chunks FSG gfs0 K0D) (conj (as0_art_rt_sec FSG gfs0 K0D) (conj (as0_art_rt_quar FSG gfs0 K0D)
             (conj (as0_art_rt_depot FSG gfs0) (conj (as0_art_rt_ia FSG gfs0 K0D) (conj (fun b (Hb : In b []) => match Hb with end) (as0_art_rt_ghost FSG gfs0 K0D))))))))))).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs R model HC"] Lemma byteZ : forall b off n a, chk_zero (kn cs) b off n = true -> uE E b + off <= a < uE E b + off + n -> byte_at FULL a 0.
  Proof.
    intros b off n a H Ha. unfold byte_at.
    destruct (hc_zero ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model b off n HC H) as (_ & _ & Hz).
    replace a with (uE E b + off + (a - (uE E b + off))) by ring. apply Hz. lia.
  Qed.

  (* [comment removed for export] *)
  Definition KSH : Z := 0x7fff8000 + 8192 * (SPB / 65536).
  Definition as0_EXTRA : list (Z * Z) := [(KSH, KSH + 2 ^ 34)].
  Definition as0_A0x : list (Z * Z) := as0_A0 as0_EXTRA cs E.

  #[using="Type"] Lemma as0_EXTRA_wf : A_wf as0_EXTRA.
  Proof.
    unfold A_wf, as0_EXTRA, KSH, page_size. constructor; [|constructor]. cbn [fst snd].
    set (q := SPB / 65536).
    replace (2147450880 + 8192 * q) with ((524280 + 2 * q) * 4096) by ring.
    replace ((524280 + 2 * q) * 4096 + 2 ^ 34) with ((524280 + 2 * q + 4194304) * 4096) by ring.
    rewrite !Z.mod_mul by lia. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma vis_shadow_allowed : forall b n a m, vis_in cs b n = true ->
    uE E b <= a -> a + m <= uE E b + uE E n -> (uE E b + uE E n) mod 8 = 0 -> 0 < m -> 0 <= a -> a + m <= 2 ^ 47 ->
    shadow_allowed as0_A0x a m.
  Proof.
    intros b n a m Hv H1 H2 H8 Hm Ha Hhi x [X1 X2]. unfold HeapIfaceA.S, HeapIfaceA.SB in X1, X2.
    unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn.
    pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat (Z_to_bv 64 x)) as (P1 & P2 & P3).
    assert (Hx : 0 <= x < 2 ^ 64).
    { pose proof (Z.div_pos a 8 Ha ltac:(lia)). assert ((a + m - 1) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia). change (2 ^ 47 / 8) with (2 ^ 44) in *. lia. }
    rewrite u64_lit in P1, P2 by exact Hx.
    unfold as0_A0x, as0_A0, A0_of, page_allowedb. rewrite existsb_app. apply orb_true_iff. left.
    apply existsb_exists. exists (pagedown (sh_lo ASAN0 E (b, n)), pageup (sh_hi ASAN0 E (b, n))). split.
    - unfold allowA. apply in_flat_map. exists (b, n). split; [apply in_or_app; left; exact Hp|]. right. left. reflexivity.
    - cbn [fst snd]. unfold sh_lo, sh_hi, page_size. cbn [fst snd shadow_off ASAN0].
      assert (L1 : uE E b / 8 <= a / 8) by (apply Z.div_le_mono; lia).
      assert (L2 : (a + m - 1) / 8 < (uE E b + uE E n) / 8).
      { pose proof (Z.div_mod (uE E b + uE E n) 8 ltac:(lia)) as D. rewrite H8 in D.
        assert ((a + m - 1) / 8 <= (uE E b + uE E n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert ((uE E b + uE E n - 1) / 8 < (uE E b + uE E n) / 8); [|lia].
        apply Z.div_lt_upper_bound; [lia|]. lia. }
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Variables BUDGET LENMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= BatInv_b.KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + 2 ^ 34 + BUDGET <= AsanInitK.LIMIT.
  Hypothesis BUD_ge : 2 ^ 34 <= BUDGET.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs)) + BatInv_b.KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Notation MAPS0 := (vm_maps (m_vmmaps model)).
  #[local] Notation RESV0 := (segments_reserved ASEGS0).
  #[local] Notation NOACC0 := (vm_noaccess (m_vmmaps model)).
  Definition as0_BASEx : Z := as0_BASE as0_EXTRA cs.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R HC LENMAX BUD BUD_le GAP"] Theorem as0_art_binv :
    BINV AsanUbsan.M.loaded_segments MAPS0 RESV0 NOACC0 (rn_HI rn) as0_BASEx BUDGET [] as0_A0x FULL (m_vmmaps model) (m_vm_lazy model).
  Proof.
    apply BINV_intro. unfold rn_HI. cbn [as0_rn as0_ar rn_ar ar_sptop].
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    exact (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX BatInv_b.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva cs CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_shdef : forall a : word, in_shadow_rw (bv_unsigned a) -> FULL a <> None.
  Proof.
    assert (Hb : a_eager cs + a_abytes cs + A_bytes as0_EXTRA + BUDGET <= AsanInitK.LIMIT).
    { unfold as0_EXTRA. cbn [A_bytes fst snd]. lia. }
    pose proof (as0_binv_main sp brk0 rdraw argv envp uid hw fs Hsp Hva BUDGET LENMAX BatInv_b.KMAX BUD as0_EXTRA as0_EXTRA_wf cs CHK0 Hb GAP E R FULL model HC) as B.
    intros a Ha. eapply bi_shdef; [exact B | exact Ha].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma byte1 : forall a v, chk_word (kn cs) (ELit 0) a 1 (ELit v) = true -> 0 <= a < 2 ^ 64 -> 0 <= v < 2 ^ 64 -> in_shadow_rw a -> byte_at FULL a v.
  Proof.
    intros a v H Ha Hv Hs. pose proof (cellW (ELit 0) a 1 (ELit v) H) as X. rewrite uE0, (uE_lit E v Hv), Z.add_0_l in X.
    unfold cell in X. rewrite (art_bytes1 v Hv) in X. cbn [rdn] in X. unfold byte_at.
    pose proof (as0_shdef (Z_to_bv 64 a) ltac:(rewrite u64_lit by lia; exact Hs)) as D.
    destruct (FULL (Z_to_bv 64 a)) as [b|]; [|contradiction]. injection X as ->. reflexivity.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 E R model HC BUDGET LENMAX BUD BUD_le GAP"] Lemma glob_ok : forall g, glob_chk (kn cs) g = true -> shadow_blk FULL (fst g) (snd g).
  Proof.
    intros [beg size] H. cbn [fst snd]. unfold glob_chk in H. cbn [fst snd] in H. chk_split H.
    repeat match goal with X : Z.leb _ _ = true |- _ => apply Z.leb_le in X | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X end.
    assert (Q1 : 0x10000 / 8 <= beg / 8) by (apply Z.div_le_mono; lia). assert (Q2 : beg / 8 <= 0x696000 / 8) by (apply Z.div_le_mono; lia).
    change (0x10000 / 8) with 8192 in Q1. change (0x696000 / 8) with 863232 in Q2.
    assert (Q3 : 0 <= size / 8) by (apply Z.div_pos; lia). assert (Q4 : size / 8 <= 4096 / 8) by (apply Z.div_le_mono; lia). change (4096 / 8) with 512 in Q4.
    pose proof (Z.mod_pos_bound size 8 ltac:(lia)) as Q5.
    unfold shadow_blk, shadow_zero, HeapIfaceA.S, HeapIfaceA.SB. split.
    - intros j Hj. apply orb_prop in H as [H|H]; [apply Z.eqb_eq in H; lia|].
      apply (byteZ (ELit 0) (beg / 8 + 0x7fff8000) (size / 8)); [assumption | rewrite uE0; lia].
    - intros NZ. apply byte1; [match goal with X : (if Z.eqb (size mod 8) 0 then true else ?c) = true |- ?c = true => destruct (Z.eqb_spec (size mod 8) 0) as [E0|_]; [exfalso; exact (NZ E0) | exact X] end
                              | lia | lia | unfold in_shadow_rw, LSH_LO, LSH_HI; left; lia].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_c_statics : art_c_statics rn FULL.
  Proof.
    unfold art_c_statics. cbn [as0_rn as0_ar rn_tp rn_dtls]. unfold TP.
    pose proof sp0_win as W.
    pose proof (rgl I_DTLS 4096 ltac:(IDX) ltac:(chk) ltac:(lia)) as (d1 & d2 & d3 & d4).
    pose proof (xpos (bD cs) ltac:(chk)) as PD. change (uE E (bD cs)) with (rbase E cs I_DTLS) in PD.
    assert (D4 : 4096 <= rbase E cs I_DTLS) by (pose proof (Z.div_mod (rbase E cs I_DTLS) 4096 ltac:(lia)); lia).
    split; [repeat split; lia|].
    split; [CL|]. split; [CL|]. split; [CL|].
    split. { pose proof (cellW (ELit 0) (TP + 8) 8 (bD cs) ltac:(chk)) as X. rewrite uE0 in X. exact X. }
    split. { pose proof (cellW (bD cs) 24 8 (ELit TP) ltac:(chk)) as X. rewrite (uE_lit E TP) in X by (unfold TP; lia). exact X. }
    split.
    { intros x Hx. change (HeapIfaceA.S 0x10000) with 2147459072 in Hx. change (HeapIfaceA.S 0x231c0) with 2147468856 in Hx. change (HeapIfaceA.S 0x23980) with 2147469104 in Hx. change (HeapIfaceA.S 0x13bfc0) with 2147612664 in Hx. change (HeapIfaceA.S 0x13c580) with 2147612848 in Hx. change (HeapIfaceA.S 0x231e0) with 2147468860 in Hx. change (HeapIfaceA.S 0x23220) with 2147468868 in Hx. change (HeapIfaceA.S 0x232a0) with 2147468884 in Hx. change (HeapIfaceA.S 0x23300) with 2147468896 in Hx. change (HeapIfaceA.S 0x23780) with 2147469040 in Hx. change (HeapIfaceA.S 0x23880) with 2147469072 in Hx. change (HeapIfaceA.S 0x696000) with 2148314112 in Hx.
      destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      - apply (byteZ (ELit 0) 2147459072 9784); [chk | rewrite uE0; lia].
      - apply (byteZ (ELit 0) 2147468860 8); [chk | rewrite uE0; lia].
      - apply (byteZ (ELit 0) 2147468884 12); [chk | rewrite uE0; lia].
      - apply (byteZ (ELit 0) 2147469040 32); [chk | rewrite uE0; lia].
      - apply (byteZ (ELit 0) 2147469104 143560); [chk | rewrite uE0; lia].
      - apply (byteZ (ELit 0) 2147612848 701264); [chk | rewrite uE0; lia]. }
    split; [|exact as0_shdef].
    assert (HG : forallb (glob_chk (kn cs)) ART_GLOBALS = true) by chk.
    apply Forall_forall. intros g Hg. exact (glob_ok g (proj1 (forallb_forall _ _) HG g Hg)).
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R model HC HGEO_STK HSP16 BUDGET LENMAX BUD BUD_le GAP"] Theorem as0_art_fsinv : art_fsinv_handoff -> art_fsinv rn art_fsg0 [] [] FULL.
  Proof.
    intros FSH. apply FSH; cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs]; unfold TP.
    - (* [comment removed for export] *)
      unfold art_fs_geo, rn_HI, app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES. cbn [as0_rn as0_ar rn_ar rn_t rn_tp ar_fs ar_sptop]. unfold TP.
      pose proof sp0_win as W. RG I_FAKE 0xb09000. RA I_FAKE I_THREAD 0xb09000 4096. RG I_THREAD 4096.   (* [comment removed for export] *)
      destruct G as (f1 & f2 & f3 & f4 & f5 & f6). specialize (f6 ltac:(unfold I_FAKE; lia)).
      pose proof (xpos (bF cs) ltac:(chk)) as PF. change (uE E (bF cs)) with (rbase E cs I_FAKE) in PF.
      assert (F4 : 4096 <= rbase E cs I_FAKE) by (pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)); lia).
      repeat split; lia.
    - pose proof (wrK (bF cs) 0 0xb09000 ltac:(chk)) as W. rewrite Z.add_0_r in W. exact W.
    - pose proof (cellW (ELit 0) TP 8 (bF cs) ltac:(chk)) as X. rewrite uE0 in X. exact X.
    - exact (cellW (bT cs) 72 8 (bF cs) ltac:(chk)).
    - pose proof (cellW (bF cs) 88 8 (ELit 20) ltac:(chk)) as X. rewrite (uE_lit E 20) in X by lia. exact X.
    - intros a Ha Hn. change (rbase E cs I_FAKE) with (uE E (bF cs)) in *.
      destruct (Z_lt_dec a (uE E (bF cs) + 88)).
      + apply (byteZ (bF cs) 0 88); [chk | lia].
      + apply (byteZ (bF cs) 96 (4096 + 32768 - 96)); [chk | lia].
    - exact as0_art_c_statics.                                                   (* [comment removed for export] *)
  Qed.

  #[using="LENMAX BUD_ge GAP"] Theorem as0_art_credit : forall (FSG : Type) (gfs0 : FSG), art_credit_ok FSG BUDGET rn (art_gs0 FSG gfs0 K0D) [] (8192, 2 ^ 34).
  Proof.
    intros FSG gfs0. unfold art_credit_ok, art_nret, art_nq, BatInv_b.KMAX, K0D.
    cbn [art_gs0 g_log g_sec g_depot g_cls g_qt g_qg app fst snd length art_cost_sum fold_right art_live fold_left].
    unfold art_cls0. cbn [cl_mu cl_free cl_cache length]. change (Z.of_nat 0) with 0. change (Z.of_nat 16384) with 16384.
    repeat split; try lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R model HC HGEO_STK HSP16 HSPA BUDGET LENMAX GAP"] Theorem as0_art_client : art_client_ok rn [] [] [] as0_A0x FULL.
  Proof.
    unfold art_client_ok. cbn [as0_rn as0_ar rn_ar ar_sptop ar_fs ar_stack_top ar_stack_bottom map].
    pose proof sp0_win as W. destruct HGEO_STK as (S1 & S2 & S3 & S4 & S5).
    pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
    pose proof (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UT. pose proof (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP) as UL.
    pose proof (utop_bounds E) as UB.
    repeat match goal with |- _ /\ _ => split end; try lia.
    - intros b [].
    - constructor.
    - (* [comment removed for export] *)
      apply (vis_shadow_allowed e_top e_stk_len); [chk | lia | lia | rewrite UT, UL; replace (utop E + (2 ^ 47 - utop E)) with (2 ^ 47) by ring; reflexivity | lia | lia | lia].
    - (* [comment removed for export] *)
      RG I_FAKE 0xb09000. destruct G as (f1 & f2 & f3 & f4 & f5 & f6).
      apply (vis_shadow_allowed (bF cs) (ELit 0xb09000)); change (uE E (bF cs)) with (rbase E cs I_FAKE); rewrite ?(uE_lit E 0xb09000) by lia; unfold FS_BYTES; try lia; [chk|].
      pose proof (Z.div_mod (rbase E cs I_FAKE) 4096 ltac:(lia)) as D. rewrite f1 in D.
      replace (rbase E cs I_FAKE + 11571200) with ((512 * (rbase E cs I_FAKE / 4096) + 1446400) * 8) by lia. apply Z.mod_mul. lia.
    - (* [comment removed for export] *)
      apply (vis_shadow_allowed (ELit 0x10000) (ELit 0x686000)); rewrite ?(uE_lit E 0x10000), ?(uE_lit E 0x686000) by lia; try lia; [chk | reflexivity].
    (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis CHKZ : art_lazy_chk cs = true.
  #[local] Notation PARR := (rbase E cs I_PARR).
  #[local] Notation BLKB := (rbase E cs I_BLK).
  #[local] Notation RIS := (SPB + 2 ^ 37).

  #[using="CHKZ"] Lemma lazy_parts : exists h1 h2, a_hlz cs = h1 ++ HSub (E_RISX cs) (ELit 4096) :: h2 /\ forallb (hop_pre cs) h1 = true
    /\ forallb (hop_zone cs) (a_hlz cs) = true
    /\ forallb (fun p => vis_hi (kn cs) p && own_ok cs p)%bool (a_vis cs ++ a_ghost cs) = true
    /\ 12 <= ealign (kn cs) (bBLK cs) /\ vis_in cs (bBLK cs) (ELit 0x800000) = true.
  Proof.
    pose proof CHKZ as H. unfold art_lazy_chk in H.
    apply andb_prop in H as [H C5]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
    destruct (hsplit (E_RISX cs) (a_hlz cs)) as [[h1 h2]|] eqn:Hs; [|discriminate].
    exists h1, h2. split; [exact (hsplit_eq _ _ _ _ Hs)|]. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
    split; [apply Z.leb_le; exact C4 | exact C5].
  Qed.

  #[using="Type"] Lemma is_rng_sound : forall b n b0 L, is_rng b n b0 L = true -> 0 <= L < 2 ^ 64 -> uE E b = uE E b0 /\ uE E n = L.
  Proof.
    intros b n b0 L H HL. unfold is_rng in H. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. subst.
    split; [reflexivity | apply uE_lit; exact HL].
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL model HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP"] Lemma ris_val2 : uE E (E_RISX cs) = RIS.
  Proof.
    unfold E_RISX, uE. cbn [edenot]. rewrite u_add64. cbn [edenot]. rewrite (u64_lit 0x2000010000) by lia.
    pose proof sp0_win. destruct HGEO_SPB as ((K1 & K2) & _).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    unfold uE in *. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="CHK0"] Lemma hlz_ok : hops_in_maps (a_maps cs) (a_hlz cs) = true.
  Proof. pose proof CHK0 as H. unfold as0_chk in H. repeat (apply andb_prop in H as [H ?]). assumption. Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma lazy_piece : forall q, In q (m_vm_lazy model) ->
    let b := bv_unsigned (fst q) in let e := bv_unsigned (fst q) + bv_unsigned (snd q) in
    ((BLKB <= b /\ e <= BLKB + 0x800000) \/ (PARR <= b /\ e <= PARR + 0x800000) \/ (KB <= b /\ e <= KB + 0x2000011000)
     \/ (0x7fff7000 <= b /\ e <= 0x10007fff8000))
    /\ (e <= RIS \/ RIS + 4096 <= b) /\ b < e.
  Proof.
    intros q Hq. cbv zeta. rewrite (hb_lazy ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) in Hq.
    destruct lazy_parts as (h1 & h2 & Hsplit & Hpre & Hzone & _).
    pose proof (hl_hops_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model (a_hlz cs) HC nofog hlz_ok) as WF.
    destruct (hl_replay E (a_hlz cs) WF q Hq) as (P1 & P2 & b & n & Hb & P3 & P4).
    split; [|split; [|lia]].
    - pose proof (proj1 (forallb_forall _ _) Hzone (HCons b n) Hb) as Hz. cbn [hop_zone] in Hz.
      repeat (apply orb_prop in Hz as [Hz|Hz]).
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. left. change (uE E (bBLK cs)) with BLKB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. left. change (uE E (bP cs)) with PARR in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. right. right. left. change (uE E (bKS cs)) with KB in E1. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x7fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x8fff7000) in E1 by lia. right. right. right. lia.
      + destruct (is_rng_sound _ _ _ _ Hz ltac:(lia)) as [E1 E2]. rewrite (uE_lit E 0x2008fff7000) in E1 by lia. right. right. right. lia.
    - rewrite Hsplit in Hq, WF.
      pose proof (hl_replay_sub E h1 (E_RISX cs) (ELit 4096) h2 WF) as SUB. rewrite ris_val2, (uE_lit E 4096) in SUB by lia.
      apply SUB; [|exact Hq]. intros b' n' Hin.
      pose proof (proj1 (forallb_forall _ _) Hpre (HCons b' n') Hin) as Hp. cbn [hop_pre] in Hp.
      destruct HGEO_SPB as ((K1 & K2) & _).
      apply orb_prop in Hp as [Hp|Hp]; destruct (is_rng_sound _ _ _ _ Hp ltac:(lia)) as [E1 E2]; rewrite E1, E2.
      + change (uE E (bBLK cs)) with BLKB.
        destruct (ra I_BLK I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
      + change (uE E (bP cs)) with PARR.
        destruct (ra I_PARR I_KSPACE 0x800000 0x2000011000 ltac:(IDX) ltac:(IDX) ltac:(IDX) ltac:(chk) ltac:(chk) ltac:(lia) ltac:(lia)) as [X|X]; [left | right]; lia.
  Qed.

  #[using="Type"] Lemma pb_facts : forall x : word, bv_unsigned (page_base x) <= bv_unsigned x < bv_unsigned (page_base x) + 4096 /\ bv_unsigned (page_base x) mod 4096 = 0.
  Proof.
    intros x. pose proof (page_base_le (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat x) as (P1 & P2 & P3). auto.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma as0_lazy_c1 : forall (FSG : Type) (gfs0 : FSG) (k0 : nat) (w : word),
    page_in_ranges (page_base w) (m_vm_lazy model) = true -> art_lazy_zone FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w).
  Proof.
    intros FSG gfs0 k0 w Hl. destruct (hl_page_piece w _ Hl) as (q & Hq & Q1 & Q2).
    destruct (pb_facts w) as ((P1 & P2) & _). destruct (lazy_piece q Hq) as (Hz & Hr & _). cbv zeta in Hz, Hr.
    destruct HGEO_SPB as ((K1 & K2) & _).
    assert (NC : ~ (RIS <= bv_unsigned w < RIS + 4096)) by lia.
    assert (NCOM : ~ art_committed FSG rn (art_gs0 FSG gfs0 k0) (bv_unsigned w)).
    { unfold art_committed, rn_ris, rn_spb. cbn [as0_rn as0_ar rn_ar rn_qs ar_space_beg art_gs0 g_cls g_sec_committed]. unfold art_cls0. cbn [cl_mu cl_mfa].
      rewrite spb_qs. intros [X|[(c & _ & [X|X])|(X & _)]]; [exact (NC X) | lia | lia | discriminate X]. }
    unfold art_lazy_zone. cbn [as0_rn as0_ar rn_ar rn_blk rn_kbase rn_parr]. change (2 ^ 23) with 0x800000.
    destruct Hz as [Z|[Z|[Z|Z]]].
    - right. left. lia.
    - right. right. split; [right; lia | exact NCOM].
    - right. right. split; [left; lia | exact NCOM].
    - left. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma win_nolazy : forall lo hi, lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    (forall q, In q (m_vm_lazy model) -> bv_unsigned (fst q) + bv_unsigned (snd q) <= lo \/ hi <= bv_unsigned (fst q)) ->
    forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false.
  Proof.
    intros lo hi Hlo Hhi Hap x Hx. destruct (page_in_ranges (page_base x) (m_vm_lazy model)) eqn:Hl; [exfalso | reflexivity].
    destruct (hl_page_piece x _ Hl) as (q & Hq & Q1 & Q2). destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    destruct (Hap q Hq) as [X|X]; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma apx_sound : forall zb zn p, apx (kn cs) zb zn p = true -> 0 <= zn < 2 ^ 64 ->
    (uE E zb + zn <= uE E (fst p) \/ uE E (fst p) + uE E (snd p) <= uE E zb) /\ 0 < uE E (snd p) /\ uE E (fst p) + uE E (snd p) <= 2 ^ 64.
  Proof.
    intros zb zn p H Hzn. unfold apx in H. destruct (split_lit zb) as [zb' zk] eqn:Hz. destruct (split_lit (fst p)) as [pb pk] eqn:Hp.
    apply andb_prop in H as [H Hap]. apply andb_prop in H as [Fz Fp].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) zb' zk (ELit zn) HK Fz) as (A1 & A2 & A3).
    pose proof (flat_x_sound ASEGS0 E _ (kn cs) pb pk (snd p) HK Fp) as (B1 & B2 & B3).
    pose proof (split_lit_denot E _ zb' zk Hz) as Dz. pose proof (split_lit_denot E _ pb pk Hp) as Dp.
    cbn [edenot] in A2, A3. rewrite (u64_lit zn) in A2, A3 by lia.
    assert (Ez : uE E zb = estart E (SA zb' zk)).
    { unfold uE. rewrite Dz. unfold estart in *; cbn [a_base a_off] in *. rewrite u64_lit by lia. reflexivity. }
    assert (Ep : uE E (fst p) = estart E (SA pb pk)).
    { unfold uE. rewrite Dp. unfold estart in *; cbn [a_base a_off] in *. pose proof (u64_range (edenot E (snd p))). rewrite u64_lit by lia. reflexivity. }
    pose proof (ranges_apart_x_sound ASEGS0 E _ (kn cs) _ _ _ _ _ _ HK Hap) as D.
    unfold elenZ in D. cbn [edenot] in D. rewrite (u64_lit zn) in D by lia. rewrite <- Ez, <- Ep in D.
    split; [exact D|]. split; [exact B3|]. rewrite Ep. unfold uE. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs R FULL model HC BUDGET LENMAX GAP"] Lemma vis_hi_sound : forall p, vis_hi (kn cs) p = true -> uE E (fst p) + uE E (snd p) <= 2 ^ 47.
  Proof.
    intros p H. unfold vis_hi in H. apply orb_prop in H as [H|H].
    - apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply expr_eqb_eq in H2. rewrite H1, H2.
      pose proof (isp_facts_of ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC) as ISP.
      rewrite (u_e_top ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP), (u_e_stk_len ASEGS0 ASAN0 asan0_res_len asan0_hull_ok E ISP). lia.
    - destruct (xhi (kn cs) (fst p)) as [hi|] eqn:Hx; [|discriminate]. destruct (snd p) as [n| | | | | | |] eqn:Hn; try discriminate.
      apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
      pose proof (xhi_sound ASEGS0 E _ (kn cs) (fst p) hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) Hx) as X.
      unfold uE. cbn [edenot]. rewrite (u64_lit n) by lia. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_apart : forall b n zl zh, zl mod 4096 = 0 -> zh mod 4096 = 0 -> (zh <= b \/ b + n <= zl) ->
    zh <= pagedown b \/ pageup (b + n) <= zl.
  Proof.
    intros b n zl zh Hl Hh Hap. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct Hap as [X|X]; [left | right]; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_al : forall z, pagedown z mod 4096 = 0 /\ pageup z mod 4096 = 0 /\ pagedown z <= z <= pageup z.
  Proof.
    intros z. unfold pagedown, pageup. rewrite !Z.mod_mul by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    repeat split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  #[using="cs E BUDGET LENMAX GAP"] Lemma round_id : forall z, z mod 4096 = 0 -> pagedown z = z /\ pageup z = z.
  Proof.
    intros z Hz. unfold pagedown, pageup.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    split; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Lemma own_window : forall p, In p (a_vis cs ++ a_ghost cs) ->
    let lo := pagedown (uE E (fst p)) in let hi := pageup (uE E (fst p) + uE E (snd p)) in
    (BLKB <= lo /\ hi <= BLKB + 0x800000)
    \/ (forall x : word, lo <= bv_unsigned x < hi -> page_in_ranges (page_base x) (m_vm_lazy model) = false).
  Proof.
    intros p Hp. cbv zeta. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & HalB & _).
    pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [_ Hown].
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    pose proof (rgl I_PARR 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (p1 & p2 & p3 & p4).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    destruct HGEO_SPB as ((K1 & K2) & K3).
    unfold own_ok in Hown. apply orb_prop in Hown as [Hown|Hown]; [apply orb_prop in Hown as [Hown|Hown]|].
    - (* [comment removed for export] *)
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      left. rewrite R1, R2. lia.
    - (* [comment removed for export] *)
      destruct (is_rng_sound _ _ _ _ Hown ltac:(lia)) as [E1 E2]. rewrite E1, E2, ris_val2.
      assert (RA4 : RIS mod 4096 = 0).
      { pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. replace RIS with ((16 * (SPB / 65536) + 33554432) * 4096) by lia. apply Z.mod_mul. lia. }
      destruct (round_id RIS RA4) as [R1 _]. destruct (round_id (RIS + 4096) ltac:(rewrite Z.add_mod, RA4 by lia; reflexivity)) as [_ R2].
      right. rewrite R1, R2. apply win_nolazy; [exact RA4 | rewrite Z.add_mod, RA4 by lia; reflexivity |].
      intros q Hq. destruct (lazy_piece q Hq) as (_ & Hr & _). exact Hr.
    - (* [comment removed for export] *)
      apply andb_prop in Hown as [Hown HB]. apply andb_prop in Hown as [HK HP].
      destruct (apx_sound _ _ _ HK ltac:(lia)) as (AK & NPOS & NW). destruct (apx_sound _ _ _ HP ltac:(lia)) as (AP & _ & _).
      change (uE E (bKS cs)) with KB in AK. change (uE E (bP cs)) with PARR in AP.
      set (b := uE E (fst p)) in *. set (n := uE E (snd p)) in *.
      destruct (round_al b) as (L1 & _ & L3). destruct (round_al (b + n)) as (_ & H2 & H3).
      (* [comment removed for export] *)
      pose proof CHK0 as C0. unfold as0_chk in C0. repeat (apply andb_prop in C0 as [C0 ?]).
      match goal with Hf : forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true |- _ =>
        pose proof (proj1 (forallb_forall _ _) Hf p Hp) as Hband end.
      assert (ABAND : b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b).
      { pose proof (hl_off_band ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model p) as OB.
        destruct (Z_lt_le_dec b 0x7fff7000) as [Hlt|Hge].
        - left. destruct (Z_lt_le_dec 0x7fff7000 (b + n)) as [Hin|]; [exfalso | lia].
          apply (OB 0x7fff7000 HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia].
        - right. destruct (Z_lt_le_dec b 0x10007fff8000) as [Hin|]; [exfalso | lia].
          apply (OB b HC Hband); [fold b n; lia | unfold SHB_LO, SHB_LEN; lia]. }
      (* [comment removed for export] *)
      assert (ABLK : (b + n <= BLKB \/ BLKB + 0x800000 <= b) \/ (BLKB <= b /\ b + n <= BLKB + 0x800000 /\ b mod 4096 = 0 /\ n = 4096)).
      { apply orb_prop in HB as [HB|HB].
        - destruct (apx_sound _ _ _ HB ltac:(lia)) as (AB & _ & _). change (uE E (bBLK cs)) with BLKB in AB. left. fold b n in AB. lia.
        - apply andb_prop in HB as [HB1 HB2]. apply expr_eqb_eq in HB1. apply Z.leb_le in HB2.
          assert (N4 : n = 4096) by (unfold n; rewrite HB1; apply uE_lit; lia).
          destruct (ealign_sound ASEGS0 E _ (kn cs) (fst p) (co_know _ _ _ _ _ _ _ _ _ _ _ HC)) as ((EA1 & EA2) & EA3).
          assert (B4 : b mod 4096 = 0).
          { unfold b, uE. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ (2 ^ ealign (kn cs) (fst p))); [|exact EA3].
            exists (2 ^ (ealign (kn cs) (fst p) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
          pose proof (Z.div_mod b 4096 ltac:(lia)) as D1. pose proof (Z.div_mod BLKB 4096 ltac:(lia)) as D2. rewrite B4 in D1. rewrite b1 in D2.
          destruct (Z_lt_le_dec b BLKB); [left; left; lia|]. destruct (Z_lt_le_dec b (BLKB + 0x800000)); [right; (clear - ABAND AK AP B4 BUDGET D1 D2 E GAP H3 HB2 HGEO_STK K1 LENMAX N4 b b2 cs g2 g4 l l0 n p p2 p4; lia) | left; right; (clear - BUDGET E GAP LENMAX b cs l0 n p; lia)]. }
      destruct ABLK as [ABLK|(I1 & I2 & I3 & I4)].
      + right. apply win_nolazy; [exact L1 | exact H2 |].
        intros q Hq. destruct (lazy_piece q Hq) as (Hz & _ & Hne). cbv zeta in Hz, Hne.
        destruct Hz as [Z|[Z|[Z|Z]]].
        * destruct (round_apart b n BLKB (BLKB + 0x800000) b1 ltac:(rewrite Z.add_mod, b1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n PARR (PARR + 0x800000) p1 ltac:(rewrite Z.add_mod, p1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n KB (KB + 0x2000011000) g1 ltac:(rewrite Z.add_mod, g1 by lia; reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
        * destruct (round_apart b n 0x7fff7000 0x10007fff8000 ltac:(reflexivity) ltac:(reflexivity) ltac:(lia)) as [X|X]; [left | right]; lia.
      + left. destruct (round_id b I3) as [R1 _]. destruct (round_id (b + n) ltac:(rewrite I4, Z.add_mod, I3 by lia; reflexivity)) as [_ R2].
        rewrite R1, R2. lia.
  Qed.

  #[using="Type"] Lemma vis_in_In : forall b n, vis_in cs b n = true -> In (b, n) (a_vis cs ++ a_ghost cs).
  Proof.
    intros b n Hv. unfold vis_in in Hv. apply existsb_exists in Hv as (p & Hp & Hb). apply andb_prop in Hb as [Eb En].
    apply expr_eqb_eq in Eb. apply expr_eqb_eq in En. destruct p as [pb pn]. cbn [fst snd] in Eb, En. subst pb pn. apply in_or_app. left. exact Hp.
  Qed.

  (* [comment removed for export] *)
  #[using="cs E BUDGET LENMAX GAP"] Lemma win_allowed : forall (A : list (Z * Z)) lo hi (x : word), In (lo, hi) A -> lo mod 4096 = 0 -> hi mod 4096 = 0 ->
    lo <= bv_unsigned x < hi -> page_allowedb A (page_base x) = true.
  Proof.
    intros A lo hi x Hin Hlo Hhi Hx. unfold page_allowedb. apply existsb_exists. exists (lo, hi). split; [exact Hin|]. cbn [fst snd]. unfold page_size.
    destruct (pb_facts x) as ((P1 & P2) & P3).
    pose proof (Z.div_mod lo 4096 ltac:(lia)) as D1. pose proof (Z.div_mod hi 4096 ltac:(lia)) as D2.
    pose proof (Z.div_mod (bv_unsigned (page_base x)) 4096 ltac:(lia)) as D3. rewrite Hlo in D1. rewrite Hhi in D2. rewrite P3 in D3.
    apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC HGEO_SPB HGEO_STK HSP16 BUDGET LENMAX GAP CHKZ"] Theorem as0_art_lazy_ok : forall (FSG : Type) (gfs0 : FSG), art_lazy_ok FSG rn (art_gs0 FSG gfs0 K0D) as0_A0x (m_vm_lazy model).
  Proof.
    intros FSG gfs0. unfold art_lazy_ok. cbn [as0_rn as0_ar rn_ar rn_blk rn_qs]. change (2 ^ 23) with 0x800000.
    pose proof sp0_win as W. destruct HGEO_SPB as ((K1 & K2) & K3).
    pose proof (rgl I_KSPACE 0x2000011000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (g1 & g2 & g3 & g4).
    pose proof (rgl I_BLK 0x800000 ltac:(IDX) ltac:(chk) ltac:(lia)) as (b1 & b2 & b3 & b4).
    split; [exact (as0_lazy_c1 FSG gfs0 K0D)|]. split; [|split].
    - (* [comment removed for export] *)
      intros w Hw. unfold as0_A0x, as0_A0, A0_of in Hw. apply in_app_or in Hw as [Hw|Hw].
      + unfold allowA in Hw. apply in_flat_map in Hw as (p & Hp & Hwp). unfold allow1 in Hwp. destruct Hwp as [<-|[<-|[]]]; cbn [fst snd].
        * destruct (own_window p Hp) as [X|X]; [right; left; exact X | right; right; exact X].
        * left. destruct lazy_parts as (_ & _ & _ & _ & _ & Hvis & _).
          pose proof (proj1 (forallb_forall _ _) Hvis p Hp) as Hb. apply andb_prop in Hb as [Hhi _]. apply vis_hi_sound in Hhi.
          unfold sh_lo, sh_hi. cbn [shadow_off ASAN0]. pose proof (u64_range (edenot E (fst p))) as U1. pose proof (u64_range (edenot E (snd p))) as U2. unfold uE in *.
          unfold pagedown, pageup.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          split; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + unfold as0_EXTRA in Hw. destruct Hw as [<-|[]]. cbn [fst snd]. left. unfold KSH.
        pose proof (Z.div_mod SPB 65536 ltac:(lia)) as D. rewrite K3 in D. lia.
    - (* [comment removed for export] *)
      intros x Hx. apply (win_allowed as0_A0x KSH (KSH + 2 ^ 34)).
      + unfold as0_A0x, as0_A0, A0_of. apply in_or_app. right. left. reflexivity.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536)) with ((524280 + 2 * (SPB / 65536)) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. replace (2147450880 + 8192 * (SPB / 65536) + 2 ^ 34) with ((524280 + 2 * (SPB / 65536) + 4194304) * 4096) by ring. apply Z.mod_mul. lia.
      + unfold KSH. lia.
    - (* [comment removed for export] *)
      intros x Hx. destruct lazy_parts as (_ & _ & _ & _ & _ & _ & _ & Hvin).
      apply (win_allowed as0_A0x BLKB (BLKB + 0x800000)); [| exact b1 | rewrite Z.add_mod, b1 by lia; reflexivity | lia].
      unfold as0_A0x, as0_A0, A0_of. apply in_or_app. left. unfold allowA. apply in_flat_map. exists (bBLK cs, ELit 0x800000).
      split; [exact (vis_in_In _ _ Hvin)|]. unfold allow1. cbn [fst snd]. left.
      rewrite (uE_lit E 0x800000) by lia. change (uE E (bBLK cs)) with BLKB.
      destruct (round_id BLKB b1) as [R1 _]. destruct (round_id (BLKB + 0x800000) ltac:(rewrite Z.add_mod, b1 by lia; reflexivity)) as [_ R2].
      rewrite R1, R2. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Lemma role_kn : forall i L a n, (i < 17)%nat -> lit_len cs i L = true -> 0 <= L < 2 ^ 64 ->
    rbase E cs i <= a -> a + n <= rbase E cs i + L ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= a /\ a + n <= snd q.
  Proof.
    intros i L a n Hi HL HLr Ha Hn. exists (ivZ (amap_den E (role cs i))). split.
    - unfold KN0. apply in_map. apply in_or_app. right.
      rewrite (hb_maps ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model HC nofog). apply in_map. apply role_in. rewrite len17. exact Hi.
    - unfold lit_len in HL. apply expr_eqb_eq in HL. pose proof (role_lit E cs i L HL HLr) as El.
      unfold ivZ, amap_den. cbn [fst snd]. unfold rbase, rlen, uE in *. lia.
  Qed.
  #[using="cs E BUDGET LENMAX GAP"] Lemma seg_kn : forall b sz, In (Z_to_bv 64 b, Z_to_bv 64 sz) RESV0 -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 ->
    exists q, In q (KN0 MAPS0 RESV0) /\ fst q <= b /\ b + sz <= snd q.
  Proof.
    intros b sz Hin Hb Hs. exists (ivZ (Z_to_bv 64 b, Z_to_bv 64 sz)). split.
    - unfold KN0. apply in_map. apply in_or_app. left. exact Hin.
    - unfold ivZ. cbn [fst snd]. rewrite !u64_lit by lia. lia.
  Qed.

  #[using="sp brk0 rdraw argv envp uid hw fs CHK0 CHKS R FULL HC BUDGET LENMAX GAP"] Theorem as0_art_kn_ok : art_kn_ok MAPS0 RESV0 rn.
  Proof.
    unfold art_kn_ok, art_objs. cbn [as0_rn as0_ar rn_ar rn_t rn_ctx rn_kbase rn_parr rn_l2 rn_blk rn_dtls ar_fs]. unfold FS_BYTES.
    change (2 ^ 23) with 0x800000. change (2 ^ 20) with 0x100000.
    intros o Ho.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_THREAD 4096); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_CTX 0x10000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_KSPACE 0x2000011000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_PARR 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_L2 0x100000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_BLK 0x800000); [IDX | chk | lia | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply (role_kn I_FAKE 0xb09000); [IDX | chk | lia | lia | lia]|].
    rewrite asan0_res_eq.
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|Ho]; [cbn [fst snd]; apply seg_kn; [cbn [In]; repeat (first [left; reflexivity | right]) | lia | lia]|].
    destruct Ho as [<-|[]]. cbn [fst snd]. apply (role_kn I_DTLS 4096); [IDX | chk | lia | lia | lia].      (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva CHK0 R FULL HC BUDGET LENMAX BUD BUD_le GAP"] Lemma as0_art_eager : art_eager_ok [] as0_A0x (m_vm_lazy model).
  Proof. split; [eapply BINV_awf; exact as0_art_binv | intros b x []]. Qed.

  (* [comment removed for export] *)
  #[using="sp brk0 rdraw argv envp uid hw fs Hsp Hva AH CHK0 CHKL CHKS R HC HGEO_SPB HGEO_STK HSP16 HSPA LENMAX BUD BUD_le BUD_ge GAP CHKZ"] Theorem as0_art_handoff : art_fsinv_handoff ->
    art_handoff_target art_fsg MAPS0 RESV0 NOACC0 as0_BASEx BUDGET art_fsinv rn art_fsg0 K0D 8192 (2 ^ 34) as0_A0x FULL (vml_of model).
  Proof.
    intros FSH. unfold art_handoff_target, vml_of. cbn [fst snd].
    exact (conj (as0_art_alloc_rep art_fsg art_fsg0) (conj (as0_art_fsinv FSH) (conj as0_art_binv (conj (as0_art_credit art_fsg art_fsg0) (conj as0_art_client (conj as0_art_kn_ok (conj (as0_art_lazy_ok art_fsg art_fsg0) as0_art_eager))))))).
  Qed.
End Derive.
