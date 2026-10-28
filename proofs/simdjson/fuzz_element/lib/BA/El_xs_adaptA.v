(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac MState Mem Frame Cells Step Exec ImageA RzCPS RegsEquiv.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs Sj_num_akit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import PropExec CatExec CatSim AxSymExec3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import El_xs_stepG El_xs_soundG El_xs_full El_xs_core El_xs_sound.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import El_xs_coreA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2SG.
Open Scope Z_scope.

Definition TPV_XA : Z := 0x6a7e68.
Definition XS_SET_A : Z := 0x812ec.
Definition XS_CPY_A : Z := 0x812f4.
Definition XS_TLS_A : Z := 0x6c498.
Definition XS_UNW_A : Z := 0x76944.
Definition XS_UNWREAL_A : Z := 0x1433c4.
Definition XS_FSD_A : Z := 0x149f5c.
Definition XS_FLD_A : Z := 0x149ddc.
Definition XS_END_A : Z := 0x106e00.
Definition XS_FREERET_A : Z := 0x1068c4.
Definition XS_ROTOP_A : Z := 0x164000.
Definition EL_CXA_THROW_XA : Z := 0x106750.
Definition EL_EHG_XA : Z := 0x6a6478.
Definition EL_UNW_XA : Z := 0x6a7d90.
Definition EL_XDATA_XA : Z := 0x16e978.
Definition EL_XDATA2_XA : Z := 0x16e990.
Definition EL_CANARY_XA : Z := 0x6c7ea8.
Definition EL_AUXVC_XA : Z := 0x6c8100.
Definition EL_VPTR_XA : Z := 0x164598.
Definition EL_TINFO_XA : Z := 0x164570.
Definition EL_DTOR_XA : Z := 0x104dd0.

Definition el_xro_wordsA : list (Z * Z) :=
  [(0x164570, 0x167c28); (0x164578, 0x236cc); (0x164580, 0x1679d8);
   (0x1679d8, 0x167bd8); (0x1679e0, 0x2e900); (0x167bb0, 0x167c28); (0x167bb8, 0x2e9bf); (0x167bf8, 0x1051c8);
   (0x167c10, 0x10552c); (0x167c18, 0); (0x167c20, 0x167c68); (0x167c50, 0x1061a0);
   (0x167c60, 0x1055a8); (0x167c68, 0x167c28); (0x167c70, 0x2e9e1); (0x167c78, 0x167bb0);
   (0x16a000, 0x145120); (0x16a008, 0x145158); (0x16a010, 0x1451f4); (0x16a030, 0x145318); (0x16a038, 0x145400); (0x16a040, 0x145428); (0x16a058, 0x1454d4);
   (0x16a128, 0x16ea38); (0x16a1d8, 0); (0x16ae98, 0x16a128); (0x16aeb8, 0x104dd0); (0x16af38, 0x16e998); (0x16af40, 0x16e990); (0x16afd8, 0x6c7ea8)].
Definition el_xroA (m : word -> option byte) : Prop :=
  Forall (fun p => ro_cells asegs m (fst p) [C8 (Z_to_bv 64 (snd p))]) el_xro_wordsA.
Definition kn_xroA : list kentry := map (fun p => KWord (SA (ELit 0) (fst p)) 8 (ELit (snd p))) el_xro_wordsA.

Definition el_xdata_wordsA : list (Z * Z) := [(EL_XDATA_XA, 0x1679d8); (EL_XDATA_XA + 8, 0x106ecc); (EL_XDATA2_XA, 0xe9ccc); (EL_XDATA2_XA + 8, 0xe9dd8)].
Definition el_xdataA (m : word -> option byte) : Prop :=
  rw_cells asegs m EL_XDATA_XA [C8 (Z_to_bv 64 0x1679d8); C8 (Z_to_bv 64 0x106ecc)] /\ rw_cells asegs m EL_XDATA2_XA [C8 (Z_to_bv 64 0xe9ccc); C8 (Z_to_bv 64 0xe9dd8)].
Definition kn_xdataA : list kentry := map (fun p => KWord (SA (ELit 0) (fst p)) 8 (ELit (snd p))) el_xdata_wordsA.

Definition el_auxv_words (x16 x6 x11 x12 x23 rnd : Z) : list word :=
  map (Z_to_bv 64) [3; 0x10040; 4; 56; 5; 11; 16; x16; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition u64sA (ws : list word) : list byte := flat_map (fun w => word_to_le_bytes 8 w) ws.
Definition el_auxvA (sp : Z) (m : word -> option byte) : Prop :=
  exists av x16 x6 x11 x12 x23 rnd,
    ro_cells asegs m EL_AUXVC_XA [C8 (Z_to_bv 64 av)] /\ bytes_at asegs m av (u64sA (el_auxv_words x16 x6 x11 x12 x23 rnd))
    /\ sp <= av /\ av + 160 <= USTACK_TOP /\ av mod 8 = 0
    /\ 0 <= x16 < 2^64 /\ 0 <= x6 < 2^64 /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.

Definition uw_bytesA (uw : bool) : list Z := if uw then [0; 1; 0; 1; 0; 1; 0; 0] else [0; 0; 0; 0; 0; 0; 0; 0].

Definition XBLK : expr := EVar 40.

Definition xspk (k : Z) : expr := if Z.eqb k 0 then XSP else EAlu ALU_ADD XSP (ELit k).
Definition XAUXV : expr := EVar 41.
Definition XS_SPLO : Z := -16384.

Inductive hval : Type := HVlit (z : Z) | HVsp (k : Z) | HVopq.
Definition hcellA : Type := (Z * nat * hval)%type.
Definition hv_expr (k : nat) (v : hval) : expr :=
  match v with HVlit z => ELit z | HVsp o => xspk o | HVopq => EVar (49 + k) end.
Fixpoint kn_hcellsA (k : nat) (hcs : list hcellA) : list kentry :=
  match hcs with
  | [] => []
  | (o, w, HVopq) :: tl => KWord (SA XSP o) w (EVar (49 + k)) :: kn_hcellsA (S k) tl
  | (o, w, v) :: tl => KWord (SA XSP o) w (hv_expr k v) :: kn_hcellsA k tl
  end.

Section Frame.
Variable FSZ : Z.
Definition xs_WA : list wrange :=
  [(XSP, XS_SPLO, FSZ); (XBLK, 0, 144); (ELit 0, EL_EHG_XA, EL_EHG_XA + 12); (ELit 0, EL_UNW_XA, EL_UNW_XA + 8)].
Definition xs_CWA : list wrange :=
  [(XBLK, 0, 144); (ELit 0, EL_EHG_XA, EL_EHG_XA + 12); (ELit 0, EL_UNW_XA, EL_UNW_XA + 8); (ELit 0, EL_XDATA_XA, EL_XDATA_XA + 16); (ELit 0, EL_XDATA2_XA, EL_XDATA2_XA + 16);
   (ELit 0, EL_CANARY_XA, EL_CANARY_XA + 8); (ELit 0, EL_AUXVC_XA, EL_AUXVC_XA + 8); (XAUXV, 0, 160)].

Definition xs_regs0A (RA : Z) : list expr :=
  [ELit 0; ELit RA; XSP; EVar 3; ELit TPV_XA; EVar 5; EVar 6; EVar 7; EAlu ALU_ADD XBLK (ELit 128); EVar 9;
   EAlu ALU_ADD XBLK (ELit 128); ELit EL_TINFO_XA; ELit EL_DTOR_XA; EVar 13; EVar 14; EVar 15; EVar 16; EVar 17; EVar 18; EVar 19;
   EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].

Definition kn_geomA : list kentry :=
  [KRange XSP 0x700000000000 0x800000000000; KAlign XSP 16;
   KRange XBLK 16 0x7fffff800000; KAlign XBLK 16;
   KRange XAUXV 0x700000000000 0x7fffffffff60; KAlign XAUXV 8;
   KDisj (SA XSP XS_SPLO) (ELit (- XS_SPLO + FSZ)) (SA XBLK 0) (ELit 144);
   KDisj (SA XSP XS_SPLO) (ELit (- XS_SPLO + FSZ)) (SA XAUXV 0) (ELit 160);
   KDisj (SA XBLK 0) (ELit 144) (SA XAUXV 0) (ELit 160);
   KDisj (SA XBLK 0) (ELit 144) (SA (ELit 0) 0x10000) (ELit 0x6ba000)].
Definition kn_wrA : list kentry :=
  [KWr (SA XSP XS_SPLO) (ELit (- XS_SPLO + FSZ)); KWr (SA XBLK 0) (ELit 144); KWr (SA (ELit 0) EL_EHG_XA) (ELit 12); KWr (SA (ELit 0) EL_UNW_XA) (ELit 8)].
Definition kn_imgA : list kentry := [KImg 0x10000 XS_ROTOP_A].
Definition kn_blkA : list kentry :=
  kzeros XBLK 0 128 ++ [KWord (SA XBLK 128) 8 (ELit EL_VPTR_XA); KWord (SA XBLK 136) 4 (EVar 48); KWord (SA XBLK 140) 4 (ELit 0)].
Definition kn_ehgA : list kentry := [KWord (SA (ELit 0) EL_EHG_XA) 8 (ELit 0); KWord (SA (ELit 0) (EL_EHG_XA + 8)) 4 (ELit 0)].
Fixpoint kbytesA (a : Z) (bs : list Z) : list kentry :=
  match bs with [] => [] | b :: bs' => KWord (SA (ELit 0) a) 1 (ELit b) :: kbytesA (a + 1) bs' end.
Definition kn_unwA (uw : bool) : list kentry := kbytesA EL_UNW_XA (uw_bytesA uw).
Definition kn_cellsA : list kentry :=
  [KWord (SA (ELit 0) EL_CANARY_XA) 8 (EVar 42); KWord (SA (ELit 0) EL_AUXVC_XA) 8 XAUXV].
Definition kn_auxvA : list kentry :=
  [KWord (SA XAUXV 0) 8 (ELit 3); KWord (SA XAUXV 8) 8 (ELit 0x10040);
   KWord (SA XAUXV 16) 8 (ELit 4); KWord (SA XAUXV 24) 8 (ELit 56);
   KWord (SA XAUXV 32) 8 (ELit 5); KWord (SA XAUXV 40) 8 (ELit 11);
   KWord (SA XAUXV 48) 8 (ELit 16); KWord (SA XAUXV 56) 8 (EVar 43);
   KWord (SA XAUXV 64) 8 (ELit 6); KWord (SA XAUXV 72) 8 (EVar 44);
   KWord (SA XAUXV 80) 8 (ELit 11); KWord (SA XAUXV 88) 8 (EVar 45);
   KWord (SA XAUXV 96) 8 (ELit 12); KWord (SA XAUXV 104) 8 (EVar 46);
   KWord (SA XAUXV 112) 8 (ELit 23); KWord (SA XAUXV 120) 8 (EVar 47);
   KWord (SA XAUXV 128) 8 (ELit 25); KWord (SA XAUXV 136) 8 (EVar 39);
   KWord (SA XAUXV 144) 8 (ELit 0); KWord (SA XAUXV 152) 8 (ELit 0)].
Definition xs_kn0A (hcs : list hcellA) (uw : bool) : list kentry :=
  kn_geomA ++ kn_wrA ++ kn_imgA ++ kn_blkA ++ kn_ehgA ++ kn_unwA uw ++ kn_hcellsA 0 hcs ++ kn_xdataA ++ kn_cellsA ++ kn_auxvA ++ kn_xroA.
Definition xs_ss0A (hcs : list hcellA) (RA : Z) (uw : bool) : sym_state := SS EL_CXA_THROW_XA (xs_regs0A RA) [] (xs_kn0A hcs uw) 200.

Definition xautoXA (IT : itab) := xautoA IT TPV_XA XS_SET_A XS_CPY_A XS_TLS_A XS_UNW_A XS_UNWREAL_A XS_FSD_A XS_FLD_A xs_WA xs_CWA kn_xroA XS_SPLO FSZ XS_ROTOP_A.
End Frame.

Definition lane_of (e : expr) : option (expr * nat) :=
  match e with
  | EExt false i 1 x => if Nat.eqb i 0 then Some (x, 0%nat) else None
  | EMd M_MUL (ELit c) (EExt false i 1 x) => if (Z.eqb c (2 ^ (8 * Z.of_nat i)) && Nat.leb i 7)%bool then Some (x, i) else None
  | _ => None
  end.
Fixpoint lanes_of (e : expr) (acc : list (expr * nat)) : option (list (expr * nat)) :=
  match lane_of e with
  | Some l => Some (l :: acc)
  | None => match e with
            | EAlu ALU_ADD a b => match lanes_of a acc with Some acc' => lanes_of b acc' | None => None end
            | _ => None
            end
  end.

Definition lanes_canon (x : expr) : list (expr * nat) := map (fun i => (x, i)) [7; 6; 5; 4; 3; 2; 1; 0]%nat.
Fixpoint lanes_eqb (a b : list (expr * nat)) : bool :=
  match a, b with
  | [], [] => true
  | (x, i) :: a', (y, j) :: b' => (expr_eqb x y && Nat.eqb i j && lanes_eqb a' b')%bool
  | _, _ => false
  end.
Definition lanes_complete (ls : list (expr * nat)) : option expr :=
  match ls with
  | (x, _) :: _ => if lanes_eqb ls (lanes_canon x) then Some x else None
  | [] => None
  end.
Definition unlane (e : expr) : option expr := match lanes_of e [] with Some ls => lanes_complete ls | None => None end.
Fixpoint norm1 (e : expr) : expr :=
  match e with
  | EAlu op a b => match unlane e with Some x => x | None => EAlu op (norm1 a) (norm1 b) end
  | EAluw op a b => EAluw op (norm1 a) (norm1 b)
  | EExt sx lo n a => EExt sx lo n (norm1 a)
  | _ => e
  end.

Definition norm (e : expr) : expr := norm1 (norm1 (norm1 e)).

Definition kn_word_norm (kn : list kentry) (a : saddr) (w : nat) (v : expr) : bool :=
  existsb (fun K => match K with KWord a' w' v' => (saddr_eqb a a' && Nat.eqb w w' && expr_eqb (norm v') v)%bool | _ => false end) kn.

Definition xregs_exit : Type := list (nat * expr).
Definition xstack_exit : Type := list (Z * expr).
Definition exit_checkA (FSZ : Z) (xr : xregs_exit) (xk : xstack_exit) (s : sym_state) : bool :=
  (Z.eqb (s_pc s) XS_END_A
   && match s_log s with [] => true | _ => false end
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 10))) XBLK
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 8))) XBLK
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 1))) (ELit XS_FREERET_A)
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 2))) (xspk (FSZ - 32))
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 3))) (EVar 3)
   && expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 4))) (ELit TPV_XA)
   && forallb (fun re => expr_eqb (norm (sr_get (s_regs s) (Z_to_bv 5 (Z.of_nat (fst re))))) (snd re)) xr
   && kn_word_norm (s_know s) (SA (ELit 0) EL_EHG_XA) 8 (ELit 0)
   && kn_word_norm (s_know s) (SA (ELit 0) (EL_EHG_XA + 8)) 4 (ELit 0)
   && forallb (fun i => kn_word_norm (s_know s) (SA (ELit 0) (EL_UNW_XA + Z.of_nat i)) 1 (ELit (nth i (uw_bytesA true) 0))) (seq 0 8)
   && forallb (fun ke => kn_word_norm (s_know s) (SA XSP (fst ke)) 8 (snd ke)) xk)%bool.
Definition exit_okA (FSZ : Z) (xr : xregs_exit) (xk : xstack_exit) (o : option sym_state) : bool :=
  match o with Some s => exit_checkA FSZ xr xk s | None => false end.

Definition XSA_FUEL : nat := 300000.
Definition XSA_K : nat := 160.

Definition lane_val (E : env) (l : expr * nat) : Z :=
  2 ^ (8 * Z.of_nat (snd l)) * ((uE E (fst l) / 2 ^ (8 * Z.of_nat (snd l))) mod 256).
Fixpoint lsum (E : env) (ls : list (expr * nat)) : Z := match ls with [] => 0 | l :: t => lane_val E l + lsum E t end.

Lemma lane_val_range : forall E x i, (i <= 7)%nat -> 0 <= lane_val E (x, i) <= 2 ^ (8 * Z.of_nat i) * 255.
Proof.
  intros E x i Hi. unfold lane_val. cbn [fst snd].
  pose proof (Z.mod_pos_bound (uE E x / 2 ^ (8 * Z.of_nat i)) 256 ltac:(lia)). split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia].
Qed.

Lemma lane_of_sound : forall E e l, lane_of e = Some l -> uE E e = lane_val E l /\ (snd l <= 7)%nat.
Proof.
  intros E e l H. unfold lane_of in H.
  destruct e as [| | | |op a b| |sx i n x|]; try discriminate.
  -   destruct op; try discriminate. destruct a as [c| | | | | | |]; try discriminate. destruct b as [| | | | | |sx i n x|]; try discriminate.
    destruct sx; [discriminate|]. destruct n as [|[|]]; try discriminate.
    destruct (Z.eqb c (2 ^ (8 * Z.of_nat i)) && Nat.leb i 7)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hc Hi]. apply Z.eqb_eq in Hc. apply Nat.leb_le in Hi. subst c. cbn [fst snd]. split; [| exact Hi].
    unfold uE. cbn [edenot]. rewrite u_mul64. rewrite u_small.
    2:{ split; [apply Z.pow_nonneg; lia|]. apply Z.pow_lt_mono_r; lia. }
    destruct (u_ext_zx i 1 (edenot E x)) as (U & B & _). rewrite U. replace (8 * Z.of_nat 1) with 8 in * by lia. change (2 ^ 8) with 256 in *.
    unfold lane_val. cbn [fst snd]. unfold uE. apply Z.mod_small.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x) / 2 ^ (8 * Z.of_nat i)) 256 ltac:(lia)).
    assert (2 ^ (8 * Z.of_nat i) <= 2 ^ 56) by (apply Z.pow_le_mono_r; lia).
    split; [apply Z.mul_nonneg_nonneg; lia|]. change (2 ^ 64) with (2 ^ 56 * 256). nia.
  -   destruct sx; [discriminate|]. destruct n as [|[|]]; try discriminate. destruct (Nat.eqb i 0) eqn:Hi; [|discriminate].
    apply Nat.eqb_eq in Hi. subst i. injection H as <-. cbn [fst snd]. split; [| lia].
    unfold uE, lane_val. cbn [edenot fst snd]. destruct (u_ext_zx 0 1 (edenot E x)) as (U & _ & _). rewrite U.
    replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. change (2 ^ 8) with 256. change (2 ^ 0) with 1. unfold uE. lia.
Qed.

Lemma lsum_app : forall E a b, lsum E (a ++ b) = lsum E a + lsum E b.
Proof. intros E a b. induction a as [|l a IH]; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma lsum_nonneg : forall E ls, Forall (fun l => (snd l <= 7)%nat) ls -> 0 <= lsum E ls.
Proof. intros E ls H. induction H as [|[x i] ls Hl _ IH]; cbn; [lia|]. pose proof (lane_val_range E x i Hl). lia. Qed.

Lemma lanes_of_sound : forall E e acc ls, lanes_of e acc = Some ls ->
  exists nw, ls = nw ++ acc /\ Forall (fun l => (snd l <= 7)%nat) nw /\ (lsum E nw < 2 ^ 64 -> uE E e = lsum E nw).
Proof.
  intros E e. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; intros acc ls H;
    cbn [lanes_of] in H;
    (destruct (lane_of _) as [l|] eqn:HL;
     [injection H as <-; exists [l]; destruct (lane_of_sound E _ l HL) as [U R]; split; [reflexivity|]; split; [constructor; [exact R| constructor]| intros _; cbn; rewrite U; lia] |]);
    try discriminate.
  destruct op; try discriminate.
  destruct (lanes_of a acc) as [acc'|] eqn:Ha; [|discriminate].
  destruct (IHa acc acc' Ha) as (nwa & -> & Fa & Ua). destruct (IHb _ ls H) as (nwb & -> & Fb & Ub).
  exists (nwb ++ nwa). split; [rewrite app_assoc; reflexivity|]. split; [apply Forall_app; split; assumption|].
  intros Hlt. rewrite lsum_app in Hlt |- *. pose proof (lsum_nonneg E nwa Fa). pose proof (lsum_nonneg E nwb Fb).
  unfold uE. cbn [edenot]. rewrite PropExec.alu_add. unfold PropExec.v_add. rewrite u_small; unfold uE in Ua, Ub; [rewrite Ua, Ub; lia|].
  rewrite Ua, Ub by lia. lia.
Qed.

Lemma lanes_eqb_eq : forall a b, lanes_eqb a b = true -> a = b.
Proof.
  induction a as [|[x i] a IH]; intros [|[y j] b] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply expr_eqb_eq in H1. apply Nat.eqb_eq in H2. subst. f_equal. apply IH. exact H3.
Qed.

Lemma lanes_sum : forall (n : nat) z, 0 <= z ->
  fold_right (fun (i : nat) s => 2 ^ (8 * Z.of_nat i) * ((z / 2 ^ (8 * Z.of_nat i)) mod 256) + s) 0 (rev (seq 0 n)) = z mod 2 ^ (8 * Z.of_nat n).
Proof.
  intros n z Hz. induction n as [|n IH].
  - cbn. rewrite Z.mod_1_r. reflexivity.
  - rewrite seq_S, rev_app_distr. cbn [rev app fold_right]. rewrite IH.
    replace (8 * Z.of_nat (S n)) with (8 * Z.of_nat n + 8) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    assert (P : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia). rewrite Nat.add_0_l.
    rewrite (Z.rem_mul_r z (2 ^ (8 * Z.of_nat n)) 256) by lia. lia.
Qed.

Lemma lanes_canon_sum : forall E x, lsum E (lanes_canon x) = uE E x.
Proof.
  intros E x. pose proof (lanes_sum 8 (uE E x) ltac:(unfold uE; pose proof (u64_range (edenot E x)); lia)) as X.
  cbn [seq rev app fold_right] in X. unfold lanes_canon. cbn [map lsum]. unfold lane_val. cbn [fst snd].
  replace (8 * Z.of_nat 8) with 64 in X by lia. rewrite (Z.mod_small (uE E x) (2 ^ 64)) in X by (unfold uE; apply u64_range).
  exact X.
Qed.

Lemma unlane_sound : forall E e x, unlane e = Some x -> edenot E e = edenot E x.
Proof.
  intros E e x H. unfold unlane in H. destruct (lanes_of e []) as [ls|] eqn:HL; [|discriminate].
  destruct (lanes_of_sound E e [] ls HL) as (nw & -> & F & U). rewrite app_nil_r in *.
  unfold lanes_complete in H. destruct nw as [|[y j] t]; [discriminate|].
  destruct (lanes_eqb ((y, j) :: t) (lanes_canon y)) eqn:HE; [|discriminate]. injection H as <-.
  apply lanes_eqb_eq in HE. rewrite HE in U. rewrite lanes_canon_sum in U.
  apply bv_eq. fold (uE E e). apply U. unfold uE. apply u64_range.
Qed.

Lemma norm1_sound : forall E e, edenot E (norm1 e) = edenot E e.
Proof.
  intros E e. induction e as [z|v|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|op a IHa b IHb|sx lo n a IHa|sx k i n]; cbn [norm1]; try reflexivity.
  - destruct (unlane (EAlu op a b)) as [x|] eqn:HU; [symmetry; apply unlane_sound; exact HU|]. cbn [edenot]. rewrite IHa, IHb. reflexivity.
  - cbn [edenot]. rewrite IHa, IHb. reflexivity.
  - cbn [edenot]. rewrite IHa. reflexivity.
Qed.
Lemma norm_sound : forall E e, edenot E (norm e) = edenot E e.
Proof. intros E e. unfold norm. rewrite !norm1_sound. reflexivity. Qed.

Notation mem := (word -> option byte).
Lemma estart_lit : forall E a, estart E (SA (ELit 0) a) = a.
Proof. intros E a. unfold estart. cbn [a_base a_off edenot]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. lia. Qed.
Lemma elenZ_lit' : forall E n, 0 <= n < 2^64 -> elenZ E (ELit n) = n.
Proof. intros E n H. rewrite elenZ_lit. apply Z.mod_small. exact H. Qed.

Lemma kwr_lit : forall E (m : mem) a n,
  0 <= a -> 0 <= n -> a + n < 2^64 -> wr_at asegs m a n -> kentry_ok asegs E m (KWr (SA (ELit 0) a) (ELit n)).
Proof.
  intros E m a n Ha Hn Hh (_ & _ & W). cbn [kentry_ok]. rewrite estart_lit, elenZ_lit' by lia.
  split; [unfold flat; rewrite estart_lit; lia|].
  intros d k Hd Hk. apply StoreOk.store_ok_of_all.
  - rewrite unsigned_lit by lia. lia.
  - intros x Hx. rewrite unsigned_lit in Hx by lia.
    specialize (W (bv_unsigned x - a) ltac:(lia)). replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in W by lia.
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.
Lemma kwr_var : forall E (m : mem) (v : nat) off n,
  0 <= bv_unsigned (ev E v) + off -> 0 <= n -> bv_unsigned (ev E v) + off + n < 2^64 ->
  wr_at asegs m (bv_unsigned (ev E v) + off) n -> kentry_ok asegs E m (KWr (SA (EVar v) off) (ELit n)).
Proof.
  intros E m v off n Ha Hn Hh (_ & _ & W). cbn [kentry_ok]. rewrite elenZ_lit' by lia.
  assert (ES : estart E (SA (EVar v) off) = bv_unsigned (ev E v) + off) by reflexivity.
  split; [unfold flat; rewrite ES; lia|]. rewrite ES.
  intros d k Hd Hk. apply StoreOk.store_ok_of_all.
  - rewrite unsigned_lit by lia. lia.
  - intros x Hx. rewrite unsigned_lit in Hx by lia.
    specialize (W (bv_unsigned x - (bv_unsigned (ev E v) + off)) ltac:(lia)).
    replace (bv_unsigned (ev E v) + off + (bv_unsigned x - (bv_unsigned (ev E v) + off))) with (bv_unsigned x) in W by lia.
    unfold wa in W. rewrite Z_to_bv_bv_unsigned in W. exact W.
Qed.
Lemma kword_at : forall E (m : mem) (b : expr) off (w : nat) (v : expr),
  (1 <= w <= 8)%nat -> 0 <= bv_unsigned (edenot E b) + off -> bv_unsigned (edenot E b) + off + Z.of_nat w <= 2^64 ->
  bytes_at asegs m (bv_unsigned (edenot E b) + off) (word_to_le_bytes w (edenot E v)) ->
  kentry_ok asegs E m (KWord (SA b off) w v).
Proof.
  intros E m b off w v Hw Ha Hh B. cbn [kentry_ok]. split; [lia|].
  assert (ES : estart E (SA b off) = bv_unsigned (edenot E b) + off) by reflexivity.
  split; [unfold flat; rewrite ES; lia|].
  pose proof (Mem.bytes_at_rdn asegs m _ _ 0 w B) as X.
  try (rewrite length_N_to_le_bytes in X; specialize (X ltac:(lia))).
  replace (List.skipn 0 (word_to_le_bytes w (edenot E v))) with (word_to_le_bytes w (edenot E v)) in X by reflexivity.
  cbn [Z.of_nat] in X. rewrite ?Z.add_0_r in X.
  rewrite firstn_all2 in X by (rewrite length_N_to_le_bytes; lia).
  rewrite rdn_common in X. rewrite adenot_SA. unfold wa in X. exact X.
Qed.
Lemma kimg_of_none : forall E (m : mem) lo hi,
  0 <= lo -> hi <= 2^64 -> (forall i, lo <= i < hi -> m (wa i) = None) -> kentry_ok asegs E m (KImg lo hi).
Proof. intros E m lo hi Hlo Hhi H. cbn [kentry_ok]. split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi. unfold wa in H. apply H. exact Hi. Qed.

Lemma bsegs_ro : forall i, 0x10000 <= i < XS_ROTOP_A -> ro_addr asegs (wa i) = true.
Proof.
  intros i Hi. unfold XS_ROTOP_A in Hi. unfold ro_addr. unfold wa. rewrite unsigned_lit by lia.
  unfold asegs. cbn -[Z.leb Z.add Z.of_N]. cbn [Z.of_N].
  destruct (Z.leb_spec0 65536 i); destruct (Z.leb_spec0 (i + 1) (65536 + 303104)); cbn [andb]; try reflexivity; try lia.
  destruct (Z.leb_spec0 368640 i); destruct (Z.leb_spec0 (i + 1) (368640 + 1089536)); cbn [andb]; try reflexivity; lia.
Qed.
Lemma kimg_ro_A : forall E (m : mem), mem_inv asegs m -> kentry_ok asegs E m (KImg 0x10000 XS_ROTOP_A).
Proof.
  intros E m MI. apply kimg_of_none; [lia| unfold XS_ROTOP_A; lia|]. intros i Hi.
  destruct (m (wa i)) as [b|] eqn:Em; [|reflexivity]. exfalso.
  pose proof (Mem.mem_inv_ro asegs m (wa i) b MI Em) as X. rewrite bsegs_ro in X by exact Hi. discriminate.
Qed.

Fixpoint segs_top (sg : list Segment) : Z :=
  match sg with
  | [] => 0
  | s0 :: rest => Z.max (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) (segs_top rest)
  end.
Lemma find_segment_high : forall sg a n, (1 <= n)%Z -> (segs_top sg <= a)%Z -> find_segment sg a n = None.
Proof.
  induction sg as [|s0 sg IH]; intros a n Hn Ha; [reflexivity|]. cbn [find_segment segs_top] in *.
  replace (Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. apply IH; lia.
Qed.
Lemma bsegs_top : segs_top asegs = SEGTOP_A.
Proof. reflexivity. Qed.
Lemma seg_rom_highA : forall x : word, SEGTOP_A <= bv_unsigned x -> OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS.PropExec.seg_rom asegs x = None.
Proof.
  intros x Hx. unfold PropExec.seg_rom, memory_read.
  rewrite (find_segment_high asegs); [reflexivity| lia| rewrite bsegs_top; exact Hx].
Qed.

Lemma rw_cells_bytes : forall (m : mem) A cs, rw_cells asegs m A cs -> bytes_at asegs m A (cells_bytes cs).
Proof. intros m A cs [[_ B] _]. exact B. Qed.

Lemma kbytesA_ok : forall E (m : mem) a (bs : list Z),
  0 <= a -> a + Z.of_nat (length bs) < 2^64 -> Forall (fun b => 0 <= b < 256) bs ->
  bytes_at asegs m a (map (fun b => Z_to_bv 8 b) bs) -> know_ok asegs E m (kbytesA a bs).
Proof.
  intros E m a bs. revert a. induction bs as [|b bs IH]; intros a Ha Hh HF B; [constructor|].
  cbn [kbytesA]. cbn [length] in Hh. apply Forall_cons_iff in HF as [Hb HF]. cbn [map] in B. change (Z_to_bv 8 b :: map _ bs) with ([Z_to_bv 8 b] ++ map (fun b => Z_to_bv 8 b) bs) in B.
  apply Mem.bytes_at_app in B as [B1 B2]. cbn [length Z.of_nat Pos.of_succ_nat] in B2.
  constructor.
  - assert (U0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; rewrite unsigned_lit; lia).
    apply (kword_at E m (ELit 0) a 1 (ELit b)); rewrite ?U0; [lia| lia| lia|].
    cbn [edenot]. unfold word_to_le_bytes. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes]. rewrite Z.add_0_l. exact B1.
  - apply IH; [lia| lia| exact HF| exact B2].
Qed.

Lemma kn_lits_ok : forall E (m : mem) (ws : list (Z * Z)),
  Forall (fun p => cells_at asegs m (fst p) [C8 (Z_to_bv 64 (snd p))] /\ 0 <= fst p /\ fst p + 8 <= 2^64) ws ->
  know_ok asegs E m (map (fun p => KWord (SA (ELit 0) (fst p)) 8 (ELit (snd p))) ws).
Proof.
  intros E m ws H. induction H as [|[a v] ws [[_ B] [H1 H2]] _ IH]; [constructor|]. cbn [map fst snd] in *. constructor; [| exact IH].
  assert (U0 : bv_unsigned (edenot E (ELit 0)) = 0) by (cbn [edenot]; rewrite unsigned_lit; lia).
  apply kword_at; rewrite ?U0; [lia| lia| lia|]. cbn [edenot]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite Z.add_0_l. exact B.
Qed.

Lemma stk_wr_atA : forall (m : mem) lo hi a n, stk asegs m lo hi -> lo <= a -> 0 <= n -> a + n <= hi -> wr_at asegs m a n.
Proof. intros m lo hi a n (H1 & H2 & ST) Ha Hn Hh. split; [lia|]. split; [lia|]. intros i Hi. apply (proj1 (ST (a + i) ltac:(lia))). Qed.

Lemma CLIENT_STATIC_0x6a6250 : exists hi, In (0x6a6290, hi) CLIENT_STATIC /\ 0x6a6290 + 0x22000 <= hi.
Proof. unfold CLIENT_STATIC. eexists. split; [cbn; right; right; left; reflexivity| cbn; lia]. Qed.
Lemma CLIENT_STATIC_0x16e700 : exists hi, In (0x16e760, hi) CLIENT_STATIC /\ 0x16e760 + 0x1000 <= hi.
Proof. unfold CLIENT_STATIC. eexists. split; [cbn; left; reflexivity| cbn; lia]. Qed.

Lemma xstatics_client : forall a,
  (EL_EHG_XA <= a < EL_EHG_XA + 12 \/ EL_UNW_XA <= a < EL_UNW_XA + 8 \/ EL_XDATA_XA <= a < EL_XDATA_XA + 16 \/ EL_XDATA2_XA <= a < EL_XDATA2_XA + 16
   \/ EL_CANARY_XA <= a < EL_CANARY_XA + 8 \/ EL_AUXVC_XA <= a < EL_AUXVC_XA + 8) -> client_static a.
Proof.
  intros a H. unfold EL_EHG_XA, EL_UNW_XA, EL_XDATA_XA, EL_XDATA2_XA, EL_CANARY_XA, EL_AUXVC_XA in H. unfold client_static, in_ranges.
  pose proof CLIENT_STATIC_0x6a6250 as C1. pose proof CLIENT_STATIC_0x16e700 as C2. split.
  - destruct H as [H|[H|[H|[H|[H|H]]]]].
    + destruct C1 as (hi & HIn & LO). exists 0x6a6290, hi. split; [exact HIn| lia].
    + destruct C1 as (hi & HIn & LO). exists 0x6a6290, hi. split; [exact HIn| lia].
    + destruct C2 as (hi & HIn & LO). exists 0x16e760, hi. split; [exact HIn| lia].
    + destruct C2 as (hi & HIn & LO). exists 0x16e760, hi. split; [exact HIn| lia].
    + destruct C1 as (hi & HIn & LO). exists 0x6a6290, hi. split; [exact HIn| lia].
    + destruct C1 as (hi & HIn & LO). exists 0x6a6290, hi. split; [exact HIn| lia].
  - intros (lo & hi & HIn & Hx). unfold RT_STATIC in HIn. cbn in HIn.
    repeat (destruct HIn as [HIn|HIn]; [injection HIn as <- <-; lia|]). exact HIn.
Qed.

Definition cwA (w : nat) (v : word) : cell := match w with 4%nat => C4 v | _ => C8 v end.
Fixpoint hcells_okA (m : mem) (usp : Z) (k : nat) (hcs : list hcellA) (ws : list word) : Prop :=
  match hcs with
  | [] => True
  | (o, w, HVlit z) :: tl => rw_cells asegs m (usp + o) [cwA w (Z_to_bv 64 z)] /\ 0 <= z < 2^64 /\ (w = 4%nat \/ w = 8%nat) /\ hcells_okA m usp k tl ws
  | (o, w, HVsp j) :: tl => rw_cells asegs m (usp + o) [cwA w (Z_to_bv 64 (usp + j))] /\ 0 <= j <= 4096 /\ (w = 4%nat \/ w = 8%nat) /\ hcells_okA m usp k tl ws
  | (o, w, HVopq) :: tl => rw_cells asegs m (usp + o) [cwA w (nth k ws (Z_to_bv 64 0))] /\ (w = 4%nat \/ w = 8%nat) /\ hcells_okA m usp (S k) tl ws
  end.

Section Entry.
  Variables (R : bvmap 5 word) (blk av : Z) (canary : word) (x16 x6 x11 x12 x23 rnd : Z) (code : word) (ws : list word).
  Definition xs_extraA : list word :=
    [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 rnd;
     Z_to_bv 64 blk; Z_to_bv 64 av; canary; Z_to_bv 64 x16; Z_to_bv 64 x6; Z_to_bv 64 x11; Z_to_bv 64 x12; Z_to_bv 64 x23; code] ++ ws.
  Definition xs_E0A : env :=
    Env (fun n => if (n <? 32)%nat then reg_get R (Z_to_bv 5 (Z.of_nat n)) else nth (n - 32)%nat xs_extraA (Z_to_bv 64 0)) (fun _ => []).
  Lemma xs_E0A_regn : forall n, (n < 32)%nat -> ev xs_E0A n = reg_get R (Z_to_bv 5 (Z.of_nat n)).
  Proof. intros n Hn. cbn [ev xs_E0A]. replace (n <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
  Lemma xs_E0A_hi : forall n, (32 <= n)%nat -> ev xs_E0A n = nth (n - 32)%nat xs_extraA (Z_to_bv 64 0).
  Proof. intros n Hn. cbn [ev xs_E0A]. replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. Qed.
  Lemma xs_E0A_hc : forall k, ev xs_E0A (49 + k) = nth k ws (Z_to_bv 64 0).
  Proof.
    intros k. rewrite xs_E0A_hi by lia. replace (49 + k - 32)%nat with (17 + k)%nat by lia. unfold xs_extraA.
    change (17 + k)%nat with (length [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 rnd;
     Z_to_bv 64 blk; Z_to_bv 64 av; canary; Z_to_bv 64 x16; Z_to_bv 64 x6; Z_to_bv 64 x11; Z_to_bv 64 x12; Z_to_bv 64 x23; code] + k)%nat. apply app_nth2_plus.
  Qed.
End Entry.

Lemma mkR_sel7 : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 in
  reg_get R (Z_to_bv 5 1) = x1 /\ reg_get R (Z_to_bv 5 2) = x2 /\ reg_get R (Z_to_bv 5 4) = x4 /\ reg_get R (Z_to_bv 5 8) = x8
  /\ reg_get R (Z_to_bv 5 10) = x10 /\ reg_get R (Z_to_bv 5 11) = x11 /\ reg_get R (Z_to_bv 5 12) = x12.
Proof. intros. vm_compute. repeat split; reflexivity. Qed.

Lemma know_ok_appA : forall E (m : mem) k1 k2, know_ok asegs E m k1 -> know_ok asegs E m k2 -> know_ok asegs E m (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. split; assumption. Qed.

Ltac ulA := unfold XS_SPLO, RT_STACK, STACK_WIN, USTACK_TOP, NORET_DEPTH, SEGTOP_A, EL_EHG_XA, EL_UNW_XA, EL_XDATA_XA, EL_XDATA2_XA, EL_CANARY_XA, EL_AUXVC_XA in *.

Section EntryOK.
  Variable RT : rt_sig.
  Variable Σ : rts RT.
  Variables (FSZ : Z) (hcs : list hcellA) (ws : list word) (RA : Z).
  Hypothesis FSZR : 16 <= FSZ <= 4096.
  Hypothesis HCO : forall o w v, In (o, w, v) hcs -> 0 <= o /\ o + Z.of_nat w <= FSZ.
  Hypothesis HCN : (length hcs < 100)%nat.
  Hypothesis RAR : 0 <= RA < 2^64.
  Variables (sp gp t0 t1 t2 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (blk lo spx : Z) (code : word) (uw : bool).
  Let usp := bv_unsigned sp.
  Let R := mkR (Z_to_bv 64 RA) sp gp (Z_to_bv 64 TPV_XA) t0 t1 t2 (Z_to_bv 64 (blk + 128)) s1 (Z_to_bv 64 (blk + 128)) (Z_to_bv 64 EL_TINFO_XA) (Z_to_bv 64 EL_DTOR_XA)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

  Hypothesis HB : rw_cells asegs m blk [CB 128 (repeat (Z_to_bv 8 0) 128); C8 (Z_to_bv 64 EL_VPTR_XA); C4 code; C4 (Z_to_bv 64 0)].
  Hypothesis INB : In (blk, 144) (rt_live RT Σ).
  Hypothesis RB : 0 < blk /\ blk mod 16 = 0 /\ blk + 144 <= rt_sp0 RT Σ - STACK_WIN /\ (blk + 144 <= 0x10000 \/ SEGTOP_A <= blk).

  Hypothesis ST : stk asegs m lo (usp + FSZ).
  Hypothesis LO1 : 0x7fff7f800000 <= lo.
  Hypothesis LO2 : rt_sp0 RT Σ - STACK_WIN <= lo.
  Hypothesis LO3 : lo + RT_STACK <= usp + XS_SPLO.
  Hypothesis SP1 : usp + FSZ + 0xb0 <= rt_sp0 RT Σ.
  Hypothesis SP2 : rt_sp0 RT Σ - (usp + XS_SPLO) <= NORET_DEPTH.
  Hypothesis SP3 : rt_sp0 RT Σ <= USTACK_TOP.
  Hypothesis AL : usp mod 16 = 0.

  Hypothesis MI : mem_inv asegs m.
  Hypothesis HA : ART RT Σ m.
  Hypothesis XRO : el_xroA m.
  Hypothesis EHG : rw_cells asegs m EL_EHG_XA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
  Hypothesis UNW : bytes_at asegs m EL_UNW_XA (map (fun b => Z_to_bv 8 b) (uw_bytesA uw)) /\ wr_at asegs m EL_UNW_XA 8.
  Hypothesis XD : el_xdataA m.
  Hypothesis CAN : exists g : word, cells_at asegs m EL_CANARY_XA [C8 g].
  Hypothesis AUX : el_auxvA spx m.
  Hypothesis SPX : usp + FSZ <= spx.
  Hypothesis HC : hcells_okA m usp 0 hcs ws.

  Theorem xs_entryA : exists E : env,
    CIXA RT Σ (xs_WA FSZ) xs_CWA lo XS_SPLO FSZ fc E m m (xs_ss0A FSZ hcs RA uw) (MS R F (Z_to_bv 64 EL_CXA_THROW_XA) fc None m (seg_rom asegs))
    /\ (forall k, (k < 32)%nat -> ev E k = reg_get R (Z_to_bv 5 (Z.of_nat k)))
    /\ ev E 40 = Z_to_bv 64 blk /\ (forall k, ev E (49 + k) = nth k ws (Z_to_bv 64 0)).
  Proof.
    destruct AUX as (av & y16 & y6 & y11 & y12 & y23 & rnd & AC & AB & AV1 & AV2 & AV3 & R16 & R6 & R11 & R12 & R23 & RR).
    destruct CAN as [canary CANc].
    destruct RB as (RB1 & RB2 & RB3 & RB4).
    exists (xs_E0A R blk av canary y16 y6 y11 y12 y23 rnd code ws).
    split; [| split; [intros k Hk; apply xs_E0A_regn; exact Hk| split; [reflexivity| apply xs_E0A_hc]]].
    split; [cbn; lia|].
    intros E' HAE. destruct HAE as [HAE _].
    assert (EV : forall k, (k < 200)%nat -> ev E' k = ev (xs_E0A R blk av canary y16 y6 y11 y12 y23 rnd code ws) k) by (intros k Hk; symmetry; apply HAE; exact Hk).
    destruct (mkR_sel7 (Z_to_bv 64 RA) sp gp (Z_to_bv 64 TPV_XA) t0 t1 t2 (Z_to_bv 64 (blk + 128)) s1 (Z_to_bv 64 (blk + 128)) (Z_to_bv 64 EL_TINFO_XA) (Z_to_bv 64 EL_DTOR_XA)
                a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as (Q1 & Q2 & Q4 & Q8 & Q10 & Q11 & Q12).
    assert (E2 : ev E' 2 = sp) by (rewrite EV by lia; rewrite xs_E0A_regn by lia; exact Q2).
    assert (E40 : ev E' 40 = Z_to_bv 64 blk) by (rewrite EV by lia; reflexivity).
    assert (E41 : ev E' 41 = Z_to_bv 64 av) by (rewrite EV by lia; reflexivity).
    assert (E42 : ev E' 42 = canary) by (rewrite EV by lia; reflexivity).
    assert (E43 : ev E' 43 = Z_to_bv 64 y16) by (rewrite EV by lia; reflexivity).
    assert (E44 : ev E' 44 = Z_to_bv 64 y6) by (rewrite EV by lia; reflexivity).
    assert (E45 : ev E' 45 = Z_to_bv 64 y11) by (rewrite EV by lia; reflexivity).
    assert (E46 : ev E' 46 = Z_to_bv 64 y12) by (rewrite EV by lia; reflexivity).
    assert (E47 : ev E' 47 = Z_to_bv 64 y23) by (rewrite EV by lia; reflexivity).
    assert (E39 : ev E' 39 = Z_to_bv 64 rnd) by (rewrite EV by lia; reflexivity).
    assert (E48 : ev E' 48 = code) by (rewrite EV by lia; reflexivity).
    assert (USP : uE E' XSP = usp) by (unfold uE; cbn [edenot XSP]; rewrite E2; reflexivity).
    assert (UBLK : bv_unsigned (edenot E' XBLK) = blk) by (cbn [edenot XBLK]; rewrite E40; apply unsigned_lit; ulA; lia).
    assert (UAV : bv_unsigned (edenot E' XAUXV) = av) by (cbn [edenot XAUXV]; rewrite E41; apply unsigned_lit; ulA; lia).
    assert (U0 : bv_unsigned (edenot E' (ELit 0)) = 0) by (cbn [edenot]; apply unsigned_lit; ulA; lia).
    unfold usp in *.
    exists R, F. cbn [s_pc s_regs s_log s_know s_next mem_denot xs_ss0A].
    split; [reflexivity|].
    split.
    {
      intros r. unfold R. reg_cases r;
        lazymatch goal with |- getr _ ?rr = edenot E' (sr_get (xs_regs0A RA) ?rr) =>
          let e := eval vm_compute in (sr_get (xs_regs0A RA) rr) in change (sr_get (xs_regs0A RA) rr) with e end;
        unfold getr; lazymatch goal with |- (if ?c then _ else _) = _ => let t := eval vm_compute in c in change c with t end; cbv iota;
        rewrite ?Q1, ?Q2, ?Q4, ?Q8, ?Q10, ?Q11, ?Q12;
        lazymatch goal with
        | |- _ = edenot E' (EVar ?k) => cbn [edenot]; rewrite EV by lia;
              rewrite (xs_E0A_regn R blk av canary y16 y6 y11 y12 y23 rnd code ws k) by lia; reflexivity
        | |- _ = edenot E' (ELit _) => reflexivity
        | |- _ = edenot E' (EAlu ALU_ADD (EVar 40) (ELit 128)) =>
              cbn [edenot]; rewrite E40, PropExec.alu_add; unfold PropExec.v_add; rewrite !unsigned_lit by (ulA; lia); reflexivity
        | |- _ => idtac
        end. }
    split; [exact I|].
    split.
    {
      pose proof (rw_cells_bytes _ _ _ HB) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
      destruct HB as [_ WB]. cbn [cells_size csize Nat.add] in WB.
      destruct EHG as [[_ BE] WE]. cbn [cells_bytes cbytes cells_size csize Nat.add] in BE, WE. rewrite app_nil_r in BE.
      destruct UNW as [BU WU].
      destruct XD as [[[_ BX1] _] [[_ BX2] _]]. cbn [cells_bytes cbytes] in BX1, BX2. rewrite app_nil_r in BX1, BX2.
      destruct CANc as [_ BC]. cbn [cells_bytes cbytes] in BC. rewrite app_nil_r in BC.
      destruct AC as [_ BA]. cbn [cells_bytes cbytes] in BA. rewrite app_nil_r in BA.
      unfold xs_kn0A.
      apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA;
        [| apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA; [| apply know_ok_appA]]]]]]]]].
      -   unfold kn_geomA.
        unfold know_ok. repeat apply Forall_cons; [.. | apply Forall_nil]; cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off edenot XSP XBLK XAUXV];
          rewrite ?E2, ?E40, ?E41; rewrite ?unsigned_lit by (ulA; lia);
          clear BB BE BU BX1 BX2 BC BA WB WE WU; ulA; try lia.
      -   unfold kn_wrA. constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]].
        + apply kwr_var; rewrite ?E2; try (ulA; lia). eapply stk_wr_atA; [exact ST| ulA; lia| ulA; lia| ulA; lia].
        + apply kwr_var; rewrite ?E40, ?unsigned_lit; try (ulA; lia). rewrite Z.add_0_r. exact WB.
        + apply kwr_lit; try (ulA; lia). exact WE.
        + apply kwr_lit; try (ulA; lia). exact WU.
      -   unfold kn_imgA. constructor; [apply kimg_ro_A; exact MI| constructor].
      -   unfold kn_blkA. apply know_ok_appA.
        + apply kzeros_ok; rewrite ?UBLK; try (ulA; lia). rewrite Z.add_0_r.
          apply Mem.bytes_at_app in BB as [BB1 _]. exact BB1.
        + apply Mem.bytes_at_app in BB as [_ BB2]. rewrite repeat_length in BB2. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in BB2 || idtac.
          apply Mem.bytes_at_app in BB2 as [BV BB3]. rewrite Mem.length_le8 in BB3.
          apply Mem.bytes_at_app in BB3 as [BCd BB4].
          constructor; [| constructor; [| constructor; [| constructor]]]; apply kword_at; rewrite ?UBLK; try (ulA; lia); cbn [edenot].
          * lazymatch type of BV with bytes_at _ _ ?a _ => replace (blk + 128) with a by lia end. exact BV.
          * rewrite E48. lazymatch type of BCd with bytes_at _ _ ?a _ => replace (blk + 136) with a by lia end. exact BCd.
          * lazymatch type of BB4 with bytes_at _ _ ?a _ => replace (blk + 140) with a by (cbn; lia) end. exact BB4.
      -   unfold kn_ehgA. apply Mem.bytes_at_app in BE as [BE1 BE2]. rewrite Mem.length_le8 in BE2.
        constructor; [| constructor; [| constructor]]; apply kword_at; rewrite ?U0; try (ulA; lia); cbn [edenot]; [exact BE1| exact BE2].
      -   unfold kn_unwA. apply kbytesA_ok; [ulA; lia| destruct uw; cbn; ulA; lia| destruct uw; cbn; repeat constructor; lia| exact BU].
      -
        assert (CWB : forall w x, (w = 4%nat \/ w = 8%nat) -> cells_bytes [cwA w x] = word_to_le_bytes w x /\ Z.of_nat (cells_size [cwA w x]) = Z.of_nat w).
        { intros w x [-> | ->]; cbn [cwA cells_bytes cbytes cells_size csize Nat.add]; rewrite app_nil_r; split; reflexivity. }
        assert (GEN : forall tl k, hcells_okA m (bv_unsigned sp) k tl ws -> (k + length tl < 151)%nat -> (forall o w v, In (o, w, v) tl -> In (o, w, v) hcs) -> know_ok asegs E' m (kn_hcellsA k tl)).
        { induction tl as [|[[o w] v] tl IH]; intros k0 Hk HL HIN; cbn [kn_hcellsA]; [constructor|]. cbn [length] in HL.
          pose proof (HCO _ _ _ (HIN _ _ _ ltac:(left; reflexivity))) as HB0.
          destruct v as [z|j|]; cbn [hcells_okA] in Hk.
          + destruct Hk as (RC & VR & WR & Hk). constructor; [| apply IH; [exact Hk| lia| intros; apply HIN; right; assumption]].
            destruct (CWB w (Z_to_bv 64 z) WR) as [CB1 CB2]. destruct RC as [[_ BR] _]. rewrite CB1 in BR.
            apply kword_at; rewrite ?USP; unfold uE in USP; rewrite ?USP; [destruct WR; subst w; lia| ulA; lia| ulA; lia|]. cbn [edenot]. exact BR.
          + destruct Hk as (RC & VR & WR & Hk). constructor; [| apply IH; [exact Hk| lia| intros; apply HIN; right; assumption]].
            destruct (CWB w (Z_to_bv 64 (bv_unsigned sp + j)) WR) as [CB1 CB2]. destruct RC as [[_ BR] _]. rewrite CB1 in BR.
            apply kword_at; unfold uE in USP; rewrite ?USP; [destruct WR; subst w; lia| ulA; lia| ulA; lia|].
            unfold hv_expr, xspk. destruct (Z.eqb_spec j 0).
            * cbn [edenot XSP]. rewrite E2. subst j. rewrite Z.add_0_r in BR. rewrite Z_to_bv_bv_unsigned in BR. exact BR.
            * cbn [edenot XSP]. rewrite E2, PropExec.alu_add. unfold PropExec.v_add. rewrite unsigned_lit by (ulA; lia). exact BR.
          + destruct Hk as (RC & WR & Hk). constructor; [| apply IH; [exact Hk| lia| intros; apply HIN; right; assumption]].
            destruct (CWB w (nth k0 ws (Z_to_bv 64 0)) WR) as [CB1 CB2]. destruct RC as [[_ BR] _]. rewrite CB1 in BR.
            apply kword_at; unfold uE in USP; rewrite ?USP; [destruct WR; subst w; lia| ulA; lia| ulA; lia|].
            cbn [edenot]. rewrite EV by lia. rewrite (xs_E0A_hc R blk av canary y16 y6 y11 y12 y23 rnd code ws k0). exact BR. }
        apply (GEN hcs 0%nat); [exact HC| lia| intros o w v H; exact H].
      -   unfold kn_xdataA, el_xdata_wordsA. apply kn_lits_ok.
        apply Mem.bytes_at_app in BX1 as [B1 B2]. apply Mem.bytes_at_app in BX2 as [B3 B4]. rewrite Mem.length_le8 in B2, B4.
        repeat apply Forall_cons; [.. | apply Forall_nil]; cbn [fst snd]; (split; [split; [cbn; tauto|]; cbn [cells_bytes cbytes]; rewrite app_nil_r| unfold EL_XDATA_XA, EL_XDATA2_XA; lia]);
          first [exact B1| exact B2| exact B3| exact B4].
      -   unfold kn_cellsA. constructor; [| constructor; [| constructor]]; apply kword_at; rewrite ?U0; try (ulA; lia); cbn [edenot XAUXV].
        + rewrite E42. exact BC.
        + rewrite E41. exact BA.
      -   unfold kn_auxvA. unfold el_auxv_words, u64sA in AB. cbn [map flat_map] in AB. rewrite !app_nil_r in AB.
        do 19 (let B1 := fresh "B1" in
               apply Mem.bytes_at_app in AB as [B1 AB]; rewrite length_N_to_le_bytes in AB;
               lazymatch type of AB with bytes_at _ _ (?x + ?y + ?z) _ => let w := eval cbv in (y + z) in replace (x + y + z) with (x + w) in AB by lia | _ => idtac end;
               constructor; [apply kword_at; rewrite ?UAV; [lia| ulA; lia| ulA; lia| cbn [edenot];
                 rewrite ?E43, ?E44, ?E45, ?E46, ?E47, ?E39; rewrite ?Z.add_0_r;
                 lazymatch goal with |- bytes_at _ _ ?a _ => lazymatch type of B1 with bytes_at _ _ ?a' _ => replace a with a' by lia end end; exact B1 ] |]).
        constructor; [| constructor]. apply kword_at; rewrite ?UAV; [lia| ulA; lia| ulA; lia|]. cbn [edenot]. exact AB.
      -   unfold kn_xroA. apply kn_lits_ok. unfold el_xroA in XRO. rewrite Forall_forall in XRO |- *.
        intros p Hp. split; [exact (XRO p Hp)|]. unfold el_xro_wordsA in Hp. cbn in Hp.
        repeat (destruct Hp as [<-|Hp]; [cbn; lia|]). destruct Hp. }
    split; [apply fullR_mkR|]. unfold MS. cbn [ms_mem].
    split; [exact MI|]. split; [apply wmono_refl|]. split; [intros; reflexivity|]. split; [reflexivity|].
    split.
    {
      unfold genvA. unfold El_xs_coreA.uE in *. unfold uE in USP. rewrite !USP. repeat (split; [ulA; lia|]). split.
      - intros x a Hx (wb & wlo & whi & HIn & Ha). unfold xs_CWA in HIn. cbn in HIn.
        destruct HIn as [HIn|[HIn|[HIn|[HIn|[HIn|[HIn|[HIn|[HIn|[]]]]]]]]]; injection HIn as <- <- <-; cbn [edenot XBLK XAUXV] in Ha; rewrite ?E40, ?E41, ?U0 in Ha;
          rewrite ?unsigned_lit in Ha by (ulA; lia).
        + right; right; left. exists blk, 144. split; [exact INB| lia].
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia.
        + left. ulA. lia.
      - intros x a Hx (wb & wlo & whi & HIn & Ha). unfold xs_WA in HIn. cbn in HIn.
        destruct HIn as [HIn|[HIn|[HIn|[HIn|[]]]]]; injection HIn as <- <- <-; cbn [edenot XSP XBLK] in Ha; rewrite ?E2, ?E40, ?U0 in Ha;
          rewrite ?unsigned_lit in Ha by (ulA; lia).
        + left. ulA. lia.
        + right; right; left. exists blk, 144. split; [exact INB| lia].
        + right; left. apply xstatics_client. lia.
        + right; left. apply xstatics_client. lia. }
    split; [exact HA|]. unfold El_xs_coreA.uE. unfold uE in USP. rewrite USP. exact ST.
  Qed.
End EntryOK.
