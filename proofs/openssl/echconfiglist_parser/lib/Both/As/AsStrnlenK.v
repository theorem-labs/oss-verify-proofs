(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 SymAux LibKnowFrame MemSplit LibTail RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil LazyRestrict LazySR MainMem.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Arr Step Frame MState Exec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsMemchr N6_rip
  AsLazyRun AsPrintfFirst AsSxKit AsScLib AsDrvMem AsDrvCells.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SN_FR : Z := 4400.
Definition AMEMCHR : Z := 0x5698e0.
Definition ARIP : Z := 0x1c1068.
Definition SN_RET : Z := 0x1a8b78.
Definition STOPSN : list Z := [AMEMCHR; ARIP; SN_RET].
Definition FUELN : nat := 3000.
(* [comment removed for export] *)
Definition KMAXS : Z := 2^31 - 9.

(* [comment removed for export] *)
Definition sn_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0 | 2 => EVar 0 | 11 => ELit 2147483647
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition sn_cells : list (Z * nat * Z) :=
  [(0x5eaa18, 8%nat, 0x56a5b0);   (* [comment removed for export] *)
   (0x5ea890, 8%nat, 0x5698e0);   (* [comment removed for export] *)
   (0x6aa8f8, 8%nat, 0x7fff8000); (* [comment removed for export] *)
   (0x6ab5d8, 1%nat, 0x1);        (* [comment removed for export] *)
   (0x6ab5d9, 1%nat, 0x1);        (* [comment removed for export] *)
   (0x73c523, 1%nat, 0x1)].       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition shwA : expr := EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EVar 12) (ELit 3)) (ELit 2147450880)) (ELit (-8)).
Definition shwB : expr :=
  EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 1) (EVar 12)) (ELit 3)) (ELit 2147450880)) (ELit (-8)).

Definition sn_kn (KLO KHI : Z) : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) ASP_LO ASP_HI; KWr (SA (EVar 0) (- SN_FR)) SN_FR;
   KRange (EVar 12) AHI_LO AAPP_HI; KRange (EVar 1) KLO KHI;
   KImg 0x10000 0x195000; KImg 0x571000 0x5ea000;
   KZero (SA shwA 0) (ELit 8); KZero (SA shwB 0) (ELit 8)]
  ++ kn_cells sn_cells.
Definition sn_knQ : list kentry := Eval vm_compute in sn_kn 0 63.
Definition sn_knS : list kentry := Eval vm_compute in sn_kn 64 KMAXS.

(* [comment removed for export] *)
Definition sn_r1q := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN scr0 (SS 0x1a86fc sn_sr [] sn_knQ 34) []).
Definition sn_c1q := Eval vm_compute in (carry (s_log (fst (fst sn_r1q))) sn_knQ []).
Definition sn_sr1 : list expr := Eval vm_compute in (s_regs (fst (fst sn_r1q))).
Definition sn_kn1q : list kentry := Eval vm_compute in (fst (fst sn_c1q)).
Definition sn_r1s := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN scr0 (SS 0x1a86fc sn_sr [] sn_knS 34) []).
Definition sn_c1s := Eval vm_compute in (carry (s_log (fst (fst sn_r1s))) sn_knS []).
Definition sn_kn1s : list kentry := Eval vm_compute in (fst (fst sn_c1s)).

(* [comment removed for export] *)
Definition mc_clob (i : nat) : bool :=
  match i with 5 | 6 | 7 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 28 | 29 | 30 | 31 => true | _ => false end%nat.
Definition sn_sr2 : list expr :=
  Eval vm_compute in (map (fun i => match i with
     | 10 => EAlu ALU_ADD (EVar 12) (EVar 1)
     | _ => if mc_clob i then EVar (34 + i) else nth i sn_sr1 (ELit 0) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition scrQ : scripts := SCR [true; false] [] [].
Definition sn_r2q := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN scrQ (SS 0x1ab16c sn_sr2 [] sn_kn1q 66) []).
Definition sn_c2q := Eval vm_compute in (carry (s_log (fst (fst sn_r2q))) sn_kn1q []).
Definition sn_srF : list expr := Eval vm_compute in (s_regs (fst (fst sn_r2q))).
Definition sn_kn2q : list kentry := Eval vm_compute in (fst (fst sn_c2q)).
Definition sn_scs2q : list sidecond := Eval vm_compute in (snd (fst sn_r2q)).

(* [comment removed for export] *)
Definition scrS : scripts := SCR [true] [] [].
Definition sn_r2s := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN scrS (SS 0x1ab16c sn_sr2 [] sn_kn1s 66) []).
Definition sn_c2s := Eval vm_compute in (carry (s_log (fst (fst sn_r2s))) sn_kn1s []).
Definition sn_sr2s : list expr := Eval vm_compute in (s_regs (fst (fst sn_r2s))).
Definition sn_kn2s : list kentry := Eval vm_compute in (fst (fst sn_c2s)).
Definition sn_scs2s : list sidecond := Eval vm_compute in (snd (fst sn_r2s)).

(* [comment removed for export] *)
Definition rip_clob (i : nat) : bool :=
  match i with 5 | 11 | 12 | 13 | 14 | 15 | 16 | 17 => true | _ => false end%nat.
Definition after_rip (base : nat) (sr : list expr) : list expr :=
  map (fun i => if rip_clob i then EVar (base + i) else match i with 10%nat => ELit 0 | _ => nth i sr (ELit 0) end)
      (seq 0 32).
(* [comment removed for export] *)
Definition sn_sr3 : list expr := Eval vm_compute in (after_rip 66 sn_sr2s).
Definition sn_kn3e : list kentry := Eval vm_compute in (kn_cut 0 (-4384) (-4304) 0xc04000 sn_kn2s).
Definition sn_r3s := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN (SCR [false] [] []) (SS 0x1ab304 sn_sr3 [] sn_kn3e 98) []).
Definition sn_c3s := Eval vm_compute in (carry (s_log (fst (fst sn_r3s))) sn_kn3e []).
Definition sn_sr3s : list expr := Eval vm_compute in (s_regs (fst (fst sn_r3s))).
Definition sn_kn3s : list kentry := Eval vm_compute in (fst (fst sn_c3s)).
Definition sn_scs3s : list sidecond := Eval vm_compute in (snd (fst sn_r3s)).
(* [comment removed for export] *)
Definition sn_sr4 : list expr := Eval vm_compute in (after_rip 98 sn_sr3s).
Definition sn_kn4e : list kentry := Eval vm_compute in (kn_cut 0 (-2224) (-2144) 0xc04000 sn_kn3s).
Definition sn_r4s := Eval vm_compute in (sym_exec RSEGS FUELN true STOPSN scr0 (SS 0x1a8c4c sn_sr4 [] sn_kn4e 130) []).
Definition sn_c4s := Eval vm_compute in (carry (s_log (fst (fst sn_r4s))) sn_kn4e []).
Definition sn_sr4s : list expr := Eval vm_compute in (s_regs (fst (fst sn_r4s))).
Definition sn_kn4s : list kentry := Eval vm_compute in (fst (fst sn_c4s)).

Lemma sn_itinerary :
  s_pc (fst (fst sn_r1q)) = AMEMCHR /\ snd (fst sn_r1q) = [] /\ snd (fst sn_c1q) = [] /\ s_regs (fst (fst sn_r1q)) = sn_sr1
  /\ s_pc (fst (fst sn_r1s)) = AMEMCHR /\ snd (fst sn_r1s) = [] /\ snd (fst sn_c1s) = [] /\ s_regs (fst (fst sn_r1s)) = sn_sr1
  /\ s_pc (fst (fst sn_r2q)) = SN_RET /\ snd (fst sn_r2q) = sn_scs2q /\ snd (fst sn_c2q) = []
  /\ s_pc (fst (fst sn_r2s)) = ARIP /\ snd (fst sn_r2s) = sn_scs2s /\ snd (fst sn_c2s) = []
  /\ s_pc (fst (fst sn_r3s)) = ARIP /\ snd (fst sn_r3s) = sn_scs3s /\ snd (fst sn_c3s) = []
  /\ s_pc (fst (fst sn_r4s)) = SN_RET /\ snd (fst sn_r4s) = [] /\ snd (fst sn_c4s) = [].
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma sn_srF_facts :
  nth 1 sn_srF (ELit 0) = EVar 3 /\ nth 2 sn_srF (ELit 0) = EVar 0 /\ nth 10 sn_srF (ELit 0) = EVar 1
  /\ nth 1 sn_sr4s (ELit 0) = EVar 3 /\ nth 2 sn_sr4s (ELit 0) = EVar 0 /\ nth 10 sn_sr4s (ELit 0) = EVar 1
  /\ nth 2 sn_sr2s (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-4304)) /\ nth 10 sn_sr2s (ELit 0) = EVar 12
  /\ nth 11 sn_sr2s (ELit 0) = EAlu ALU_ADD (EVar 1) (ELit 1) /\ nth 1 sn_sr2s (ELit 0) = ELit 0x1ab304
  /\ nth 2 sn_sr3s (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-2144)) /\ nth 10 sn_sr3s (ELit 0) = EVar 12
  /\ nth 11 sn_sr3s (ELit 0) = EAlu ALU_ADD (EVar 1) (ELit 1) /\ nth 1 sn_sr3s (ELit 0) = ELit 0x1a8c4c.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sn_regions : list sregion := [(SA (EVar 0) (- SN_FR), SN_FR)].

Lemma sn_cov1q : log_covered sn_regions (s_log (fst (fst sn_r1q))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_cov1s : log_covered sn_regions (s_log (fst (fst sn_r1s))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_cov2q : log_covered sn_regions (s_log (fst (fst sn_r2q))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_cov2s : log_covered sn_regions (s_log (fst (fst sn_r2s))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_cov3s : log_covered sn_regions (s_log (fst (fst sn_r3s))) = true. Proof. vm_compute. reflexivity. Qed.
Lemma sn_cov4s : log_covered sn_regions (s_log (fst (fst sn_r4s))) = true. Proof. vm_compute. reflexivity. Qed.

Definition ENV (vals : list word) : env := Env (vals_ev vals) (blobs_ev []).

(* [comment removed for export] *)
Lemma sn_scs_ok : forall vals M (s : word) (K : Z) scs,
  vals_ev vals 12 = s -> vals_ev vals 1 = Z_to_bv 64 K ->
  AHI_LO <= bv_unsigned s -> bv_unsigned s + K + 1 + 8 <= AAPP_HI -> 0 <= K ->
  In scs [sn_scs2q; sn_scs2s; sn_scs3s] ->
  scs_denot RSEGS M (ENV vals) scs.
Proof.
  intros vals M s K scs P12 P1 Hlo Hhi HK0 Hin. unfold AHI_LO, AAPP_HI in *. pose proof (u64_range s) as R.
  assert (XR : bv_unsigned (alu64 ALU_XOR s (Z_to_bv 64 (-1))) = 2^64 - 1 - bv_unsigned s).
  { cbn [alu64 alu]. rewrite bv_xor_unsigned. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615.
    rewrite N6_tac.lxor_ones64 by lia. lia. }
  assert (K1 : bv_unsigned (alu64 ALU_ADD (Z_to_bv 64 K) (Z_to_bv 64 1)) = K + 1).
  { cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2^64). rewrite (Z.mod_small K), (Z.mod_small 1), Z.mod_small; lia. }
  cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; unfold sn_scs2q, sn_scs2s, sn_scs3s, scs_denot;
    repeat (apply Forall_cons; [cbn [sc_denot edenot ev ENV branch_taken]; rewrite P12, P1 |]); try apply Forall_nil;
    unfold bv_ltu, bv_leu; rewrite ?XR, ?K1.
  all: first [ apply Z.ltb_ge; lia | apply Z.leb_le; lia | rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shw8 (x : Z) : Z := 8 * ((x / 8 + ASHADOW_BASE) / 8).

Lemma shw8_eq : forall x, 0 <= x -> shw8 x = ASHADOW_BASE + 8 * (x / 64).
Proof. intros x Hx. unfold shw8. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

Lemma sn_cells_of : forall m, ACONST m -> cells_ok m sn_cells.
Proof.
  intros m AC. acells AC.
  lazymatch goal with F6 : rw_cells asegs m AINITED_CELL _ |- _ =>
    pose proof (cells_of_C1C1 m AINITED_CELL 1 1 F6 ltac:(unfold AINITED_CELL; lia) ltac:(unfold AINITED_CELL; lia)) as [I1 I2];
    change (AINITED_CELL + 1) with 6993369 in I2 end.
  pose proof (cell_of_C1 m _ _ (ACONST_cell m ACF_ISTRLEN_CELL _ AC ltac:(in_nth))) as I3.
  unfold sn_cells, cells_ok.
  repeat apply Forall_cons; try apply Forall_nil;
    first [ apply cell_of_C8; assumption
          | unfold cell_ok; first [exact I1 | exact I2 | exact I3] ].
Qed.

Section Plain.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record snH (regs : bvmap 5 word) (mem : word -> option byte) (sp s ra : word) (K : Z) (buf : list byte) : Prop := SNH {
    R1  : getr regs 1 = ra;
    R2  : getr regs 2 = sp;
    R10 : getr regs 10 = s;
    R11 : getr regs 11 = Z_to_bv 64 2147483647;
    Rsp16 : bv_unsigned sp mod 16 = 0;
    RspLo : ASP_LO <= bv_unsigned sp;
    RspHi : bv_unsigned sp <= ASP_HI;
    (* [comment removed for export] *)
    Rstk  : stk asegs mem (bv_unsigned sp - SN_FR) (bv_unsigned sp);
    (* [comment removed for export] *)
    Rimg  : forall i, 0x10000 <= i < 0x195000 -> mem (Z_to_bv 64 i) = None;
    Rgot  : forall i, 0x571000 <= i < 0x5ea000 -> mem (Z_to_bv 64 i) = None;
    Rac   : ACONST mem;
    Rinv  : mem_inv asegs mem;
    (* [comment removed for export] *)
    Rmc   : mchrH mem s buf K 2147483647;
    RsLo  : AHI_LO <= bv_unsigned s;
    RsHi  : bv_unsigned s + K + 1 + 8 <= AAPP_HI;
    (* [comment removed for export] *)
    Rdisj : bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - SN_FR \/ bv_unsigned sp <= bv_unsigned s;
    (* [comment removed for export] *)
    Rsh0  : forall a, shw8 (bv_unsigned s) <= a < shw8 (bv_unsigned s + K) + 8 -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

  (* [comment removed for export] *)
  Record snPost (regs : bvmap 5 word) (mem : word -> option byte) (sp ra : word) (K : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := SNP {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = ra;
    P_a0  : getr regs' 10 = Z_to_bv 64 K;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - SN_FR), SN_FR)];
    P_stk : stk asegs mem' (bv_unsigned sp - SN_FR) (bv_unsigned sp);
    P_inv : mem_inv asegs mem';
    P_ac  : ACONST mem' }.

  Definition sn_vals (regs : bvmap 5 word) (sp : word) (K : Z) : list word := [sp; Z_to_bv 64 K] ++ junk_vals regs.

  Lemma sn_ev_junk : forall regs sp K i, (2 <= i < 34)%nat ->
    ev (ENV (sn_vals regs sp K)) i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))).
  Proof.
    intros regs sp K i Hi. unfold ENV, sn_vals. cbn [ev]. unfold vals_ev.
    replace i with (length [sp; Z_to_bv 64 K] + (i - 2))%nat at 1 by (cbn; lia).
    rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by lia. reflexivity.
  Qed.

  Lemma sn_regs_ok : forall regs mem sp s ra K buf, snH regs mem sp s ra K buf ->
    regs_ok (ENV (sn_vals regs sp K)) sn_sr regs.
  Proof.
    intros regs mem sp s ra K buf PH.
    destruct PH as [G1 G2 G10 G11 Hsp16 HspLo HspHi Hstk Himg Hgot Hac Hinv Hmc HsLo HsHi Hdisj Hsh0].
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sn_sr allregs32 edenot].
    1: apply getr_zero.
    2: cbn [ev ENV]; assumption.
    10: assumption.
    all: rewrite sn_ev_junk by lia; f_equal; apply bv_eq; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma shwA_denot : forall E (s : word), ev E 12 = s -> AHI_LO <= bv_unsigned s -> bv_unsigned s <= AAPP_HI ->
    bv_unsigned (edenot E shwA) = shw8 (bv_unsigned s).
  Proof.
    intros E s E12 Hlo Hhi. unfold AHI_LO, AAPP_HI in *. unfold shwA, shw8. cbn [edenot]. rewrite E12.
    cbn [alu64 alu].
    rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, !Z_to_bv_unsigned.
    change (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (2147450880 mod 2 ^ 64) with 2147450880. change ((-8) mod 2 ^ 64) with 18446744073709551608.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite ASHADOW_BASE_val.
    rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). reflexivity.
  Qed.

  Lemma shwB_denot : forall E (s : word) K, ev E 12 = s -> ev E 1 = Z_to_bv 64 K -> 0 <= K ->
    AHI_LO <= bv_unsigned s -> bv_unsigned s + K <= AAPP_HI ->
    bv_unsigned (edenot E shwB) = shw8 (bv_unsigned s + K).
  Proof.
    intros E s K E12 E1 HK Hlo Hhi. unfold AHI_LO, AAPP_HI in *. unfold shwB, shw8. cbn [edenot]. rewrite E12, E1.
    cbn [alu64 alu].
    rewrite bv_and_unsigned, bv_add_unsigned, bv_shiftr_unsigned, bv_add_unsigned, !Z_to_bv_unsigned.
    change (bv_unsigned (bv_and (Z_to_bv 64 3) (Z_to_bv 64 63))) with 3.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (2147450880 mod 2 ^ 64) with 2147450880. change ((-8) mod 2 ^ 64) with 18446744073709551608.
    rewrite (Z.mod_small K) by lia. rewrite (Z.mod_small (K + _)) by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. rewrite ASHADOW_BASE_val.
    rewrite (Z.mod_small (_ / 8 + _)) by (Z.div_mod_to_equations; lia).
    rewrite land_m8' by (Z.div_mod_to_equations; lia). rewrite (Z.add_comm K). reflexivity.
  Qed.

  Lemma shw8_range : forall x, 0 <= x < AAPP_HI -> ASHADOW_BASE <= shw8 x /\ shw8 x + 8 <= AHI_LO /\ shw8 x mod 8 = 0.
  Proof. intros x Hx. unfold AAPP_HI, AHI_LO in *. rewrite shw8_eq by lia. rewrite ASHADOW_BASE_val. Z.div_mod_to_equations. lia. Qed.

  Lemma shw8_mono : forall x y, 0 <= x <= y -> shw8 x <= shw8 y.
  Proof. intros x y H. rewrite !shw8_eq by lia. Z.div_mod_to_equations. nia. Qed.

  Lemma sn_know_ok : forall regs mem sp s ra K buf KLO KHI, snH regs mem sp s ra K buf -> KLO <= K <= KHI -> 0 <= KLO ->
    know_ok RSEGS (ENV (sn_vals regs sp K)) mem (sn_kn KLO KHI).
  Proof.
    intros regs mem sp s ra K buf KLO KHI PH HK HK0.
    destruct PH as [G1 G2 G10 G11 Hsp16 HspLo HspHi Hstk Himg Hgot Hac Hinv Hmc HsLo HsHi Hdisj Hsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    unfold AHI_LO, AAPP_HI, ASP_LO, ASP_HI in *.
    assert (E0 : ev (ENV (sn_vals regs sp K)) 0 = sp) by reflexivity.
    assert (E1 : ev (ENV (sn_vals regs sp K)) 1 = Z_to_bv 64 K) by reflexivity.
    assert (E12 : ev (ENV (sn_vals regs sp K)) 12 = s) by (rewrite sn_ev_junk by lia; exact G10).
    pose proof (shwA_denot _ s E12 ltac:(unfold AHI_LO; lia) ltac:(unfold AAPP_HI; lia)) as DA.
    pose proof (shwB_denot _ s K E12 E1 ltac:(lia) ltac:(unfold AHI_LO; lia) ltac:(unfold AAPP_HI; lia)) as DB.
    pose proof (shw8_range (bv_unsigned s) ltac:(unfold AAPP_HI; lia)) as (A1 & A2 & A3).
    pose proof (shw8_range (bv_unsigned s + K) ltac:(unfold AAPP_HI; lia)) as (B1 & B2 & B3).
    pose proof (shw8_mono (bv_unsigned s) (bv_unsigned s + K) ltac:(lia)) as AB.
    rewrite ASHADOW_BASE_val in A1, B1. unfold AHI_LO in A2, B2.
    unfold sn_kn. apply (proj2 (know_ok_app RSEGS _ _ _ _)). split.
    2:{ apply cells_know; [vm_compute; reflexivity | apply sn_cells_of; assumption]. }
    repeat (apply Forall_cons); [ .. | apply Forall_nil ].
    - apply kalign_intro; [lia|]. cbn [edenot]. rewrite E0. assumption.
    - apply krange_intro. cbn [edenot]. rewrite E0. unfold ASP_LO, ASP_HI. lia.
    - apply (kwr_of_stk_ok RSEGS _ mem (EVar 0) sp SN_FR); [exact E0 | | unfold SN_FR; lia].
      eapply astk_stk_ok; [exact Hstk | lia | lia | unfold SN_FR; lia | lia].
    - apply krange_intro. cbn [edenot]. rewrite E12. unfold AHI_LO, AAPP_HI. lia.
    - apply krange_intro. cbn [edenot]. rewrite E1, u_small by lia. lia.
    - apply kimg_intro; [lia | lia | assumption].
    - apply kimg_intro; [lia | lia | assumption].
    - eapply (kzero_intro RSEGS _ mem shwA (edenot _ shwA) 0 (ELit 8) 8); [reflexivity | reflexivity | lia | lia | rewrite DA; lia |].
      intros i Hi. rewrite DA. apply Hsh0. lia.
    - eapply (kzero_intro RSEGS _ mem shwB (edenot _ shwB) 0 (ELit 8) 8); [reflexivity | reflexivity | lia | lia | rewrite DB; lia |].
      intros i Hi. rewrite DB. apply Hsh0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mchrH_frame : forall mem m' (s sp : word) buf K n,
    mchrH mem s buf K n -> frame_mod mem m' [(Z_to_bv 64 (bv_unsigned sp - SN_FR), SN_FR)] ->
    ASP_LO <= bv_unsigned sp ->
    bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - SN_FR \/ bv_unsigned sp <= bv_unsigned s ->
    mchrH m' s buf K n.
  Proof.
    intros mem m' s sp buf K n MC FM Hsp Hdisj. pose proof (u64_range sp). pose proof (u64_range s). unfold ASP_LO, SN_FR in *.
    destruct MC. split; try assumption.
    - rewrite <- (Z_to_bv_bv_unsigned s). eapply ardn_frame; [exact FM | rewrite Z_to_bv_bv_unsigned; exact Hbuf | lia | lia |].
      intros r Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
    - unfold rodata_clear in *. eapply arange_none_frame; [exact Hro | exact FM | | lia | lia].
      intros r Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. lia.
  Qed.

  Definition sn_regions_w (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - SN_FR), SN_FR)].

  Lemma sn_regions_denot : forall vals sp, vals_ev vals 0 = sp -> ASP_LO <= bv_unsigned sp ->
    map (rdenot (ENV vals)) sn_regions = sn_regions_w sp.
  Proof.
    intros vals sp P0 Hlo. unfold ASP_LO in Hlo. unfold sn_regions, sn_regions_w, rdenot, estart, SN_FR.
    cbn [map fst snd a_base a_off edenot ev ENV]. rewrite P0. repeat f_equal; lia.
  Qed.

  Lemma sn_regions_flat : forall vals sp, vals_ev vals 0 = sp -> ASP_LO <= bv_unsigned sp -> bv_unsigned sp <= ASP_HI ->
    regions_flat (ENV vals) sn_regions.
  Proof.
    intros vals sp P0 Hlo Hhi r Hr. unfold ASP_LO, ASP_HI in *. unfold sn_regions, SN_FR in Hr. cbn [In] in Hr.
    destruct Hr as [<-|[]]; unfold flat, estart; cbn [fst snd a_base a_off edenot ev ENV]; rewrite ?P0; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sn_mem_frame : forall regs mem sp s ra K buf m',
    snH regs mem sp s ra K buf -> frame_mod mem m' (sn_regions_w sp) ->
    stk asegs m' (bv_unsigned sp - SN_FR) (bv_unsigned sp) /\ mem_inv asegs m' /\ ACONST m' /\ mchrH m' s buf K 2147483647
    /\ (forall a, shw8 (bv_unsigned s) <= a < shw8 (bv_unsigned s + K) + 8 -> m' (Z_to_bv 64 a) = Some (Z_to_bv 8 0)).
  Proof.
    intros regs mem sp s ra K buf m' PH FM.
    destruct PH as [G1 G2 G10 G11 Hsp16 HspLo HspHi Hstk Himg Hgot Hac Hinv Hmc HsLo HsHi Hdisj Hsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs. pose proof (HK0 _ _ _ _ _ Hmc) as K0.
    unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI in *.
    pose proof (shw8_range (bv_unsigned s) ltac:(unfold AAPP_HI; lia)) as (A1 & A2 & A3).
    pose proof (shw8_range (bv_unsigned s + K) ltac:(unfold AAPP_HI; lia)) as (B1 & B2 & B3).
    rewrite ASHADOW_BASE_val in A1, B1. unfold AHI_LO in A2, B2.
    split; [|split; [|split; [|split]]].
    - eapply astk_grows; [exact Hstk | unfold SN_FR; lia | lia | exact (proj2 FM)].
    - eapply amem_inv_frame; [exact Hinv | exact FM |]. constructor; [|constructor]. cbn [fst snd]. unfold SN_FR. rewrite u_small by lia. lia.
    - eapply ACONST_frame; [exact Hac | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
      unfold ivls, sn_regions_w. cbn [map fst snd]. unfold SN_FR. rewrite u_small by lia.
      constructor; [|constructor]. apply aconst_ok_high; [unfold sh, AIMG_TOP; rewrite ASHADOW_BASE_val; change (12599296 / 8) with 1574912; lia | lia].
    - eapply mchrH_frame; [exact Hmc | exact FM | unfold ASP_LO; lia | exact Hdisj].
    - intros a Ha. rewrite (proj1 FM); [apply Hsh0; exact Ha|]. cbn [outside]. split; [|exact I].
      unfold in_rng, SN_FR. rewrite !u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition renorm2 (msF : machine_state) (regs : bvmap 5 word) : machine_state :=
    {| ms_regs := mkR_of regs; ms_fregs := ms_fregs msF; ms_pc_val := ms_pc_val msF; ms_svc_pending := ms_svc_pending msF;
       ms_resv := ms_resv msF; ms_fcsr := ms_fcsr msF; ms_mem := ms_mem msF; ms_rom := ms_rom msF |}.

  Lemma lz_renorm : forall msF mo R pc M rom (KX : TSet),
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R pc M rom ->
    (forall msFn, lzok RSEGS L S Zr (mkCfg msFn mo) ->
       restrict L S msFn = MS (mkR_of R) bvmap_empty pc (Z_to_bv 32 0) None M rom ->
       hid_same L S msF msFn -> realizes RSEGS (mkCfg msFn mo) KX) ->
    realizes RSEGS (mkCfg msF mo) KX.
  Proof.
    intros msF mo R pc M rom KX OK RS HK.
    unfold restrict, restrict_by, with_mem in RS.
    pose proof (f_equal ms_regs RS) as E1. pose proof (f_equal ms_fregs RS) as E2. pose proof (f_equal ms_pc_val RS) as E3.
    pose proof (f_equal ms_svc_pending RS) as E4. pose proof (f_equal ms_resv RS) as E5. pose proof (f_equal ms_fcsr RS) as E6.
    pose proof (f_equal ms_mem RS) as E7. pose proof (f_equal ms_rom RS) as E8. cbn in E1, E2, E3, E4, E5, E6, E7, E8.
    apply (realizes_eqv RSEGS (mkCfg (renorm2 msF R) mo)).
    - apply HK.
      + destruct OK as [O1 O2 O3 O4 O5 O6 O7]. split; try assumption.
      + unfold restrict, restrict_by, with_mem, renorm2, MS. cbn. rewrite E2, E3, E4, E5, E6, E7, E8. reflexivity.
      + unfold hid_same, renorm2. cbn. intros; reflexivity.
    - apply cfg_eqv_sym. split; [|reflexivity]. unfold renorm2. repeat split; cbn; try reflexivity; try (rewrite E1; apply mkR_of_eqv); try apply fregs_eqv_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma lz_evt : forall (P : machine_state -> Prop) msF mo (KX : TSet),
    lzok RSEGS L S Zr (mkCfg msF mo) -> Exec.evt asegs P (restrict L S msF) ->
    (forall msF' mo', lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       P (restrict L S msF') -> realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) KX.
  Proof.
    intros P msF mo KX OK EV HK.
    eapply (sreach_realizes RSEGS (fun c => lzok RSEGS L S Zr c /\ same_but_materialized mo (cfg_model c) /\ hid_same L S msF (cfg_ms c) /\ P (restrict L S (cfg_ms c))));
      [eapply (evt_sreach_lazy_k RSEGS L S Zr P msF mo); [exact OK | exact EV |] |].
    - intros msF' mo' OK' SB' HS' HP'. apply sr_done. cbn [cfg_ms cfg_model]. exact (conj OK' (conj SB' (conj HS' HP'))).
    - intros [msF' mo'] (OK' & SB' & HS' & HP'). apply HK; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_wmono : forall m m' (a : word) n,
    wmono asegs m m' -> bv_unsigned a + Z.of_nat n < 2 ^ 64 -> store_ok RSEGS m a n = true -> store_ok RSEGS m' a n = true.
  Proof.
    intros m m' a n WM Hn ST. apply astore_ok_of_wview; [lia|]. intros i Hi. apply WM.
    apply (store_ok_all RSEGS m n a ltac:(lia) ST). rewrite u_small by (pose proof (u64_range a); lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mrd_high : forall m (a : Z), 0xc04000 <= a < 2 ^ 64 -> mrd asegs m (wa a) = m (Z_to_bv 64 a).
  Proof.
    intros m a Ha. unfold mrd, wa. destruct (m (Z_to_bv 64 a)); [reflexivity|].
    apply (aseg_rom_high (Z_to_bv 64 a)). rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mem_grows_of_stk : forall m m' (l h lo hi : Z),
    munch [(l, h)] m m' -> stk asegs m' lo hi -> lo <= l -> h <= hi -> 0xc04000 <= lo -> hi <= 2 ^ 64 -> mem_grows m m'.
  Proof.
    intros m m' l h lo hi MU (S1 & S2 & ST) Hl Hh Hlo Hhi x Hx. pose proof (u64_range x) as Rx.
    destruct (Z_lt_le_dec (bv_unsigned x) l) as [A|A]; [rewrite MU; [exact Hx | cbn; lia]|].
    destruct (Z_lt_le_dec (bv_unsigned x) h) as [B|B]; [|rewrite MU; [exact Hx | cbn; lia]].
    destruct (ST (bv_unsigned x) ltac:(lia)) as [_ (b & Hb)]. rewrite mrd_high in Hb by lia.
    rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma frame_mod_of_munch : forall m m' (l h : Z) (sp : word),
    munch [(l, h)] m m' -> mem_grows m m' -> bv_unsigned sp - SN_FR <= l -> h <= bv_unsigned sp -> SN_FR <= bv_unsigned sp ->
    frame_mod m m' (sn_regions_w sp).
  Proof.
    intros m m' l h sp MU MG Hl Hh Hsp. pose proof (u64_range sp). split; [|exact MG].
    intros a Ha. apply MU. cbn [outside sn_regions_w] in Ha |- *. destruct Ha as [Ha _]. unfold in_rng, SN_FR in *.
    rewrite u_small in Ha by lia. split; [|exact I]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma accessible_of_sh0 : forall m (s : Z) n,
    (forall a, shw8 s <= a < shw8 (s + n - 1) + 8 -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0)) ->
    AHI_LO <= s -> s + n <= AAPP_HI -> 1 <= n -> accessible m s n.
  Proof.
    intros m s n SH Hlo Hhi Hn. unfold AHI_LO, AAPP_HI in *. split; [lia|]. split; [unfold AAPP_HI; lia|].
    intros x Hx. exists 0. split; [lia|]. split; [|left; reflexivity].
    pose proof (shw8_range s ltac:(unfold AAPP_HI; lia)) as (A1 & A2 & A3).
    pose proof (shw8_range (s + n - 1) ltac:(unfold AAPP_HI; lia)) as (B1 & B2 & B3).
    assert (R : shw8 s <= sh x < shw8 (s + n - 1) + 8).
    { rewrite !shw8_eq by lia. unfold sh. Z.div_mod_to_equations. lia. }
    rewrite mrd_high; [| unfold AHI_LO in *; rewrite ASHADOW_BASE_val in *; lia]. rewrite (SH _ R). reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sn_head : forall knX r1 c1 (kn1 : list kentry) regs mem msF mo (sp s ra : word) K buf (KX : TSet),
    sym_exec RSEGS FUELN true STOPSN scr0 (SS 0x1a86fc sn_sr [] knX 34) [] = r1 ->
    carry (s_log (fst (fst r1))) knX [] = c1 ->
    s_pc (fst (fst r1)) = AMEMCHR -> snd (fst r1) = [] -> snd (fst c1) = [] -> s_regs (fst (fst r1)) = sn_sr1 -> fst (fst c1) = kn1 ->
    log_covered sn_regions (s_log (fst (fst r1))) = true -> kn_vars_lt 34 kn1 = true ->
    snH regs mem sp s ra K buf ->
    know_ok RSEGS (ENV (sn_vals regs sp K)) mem knX ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1a86fc) mem (seg_rom RSEGS) ->
    (forall R2 M1 msF2 mo2 vals1,
       length vals1 = 66%nat -> (forall i, (i < 34)%nat -> vals_ev vals1 i = vals_ev (sn_vals regs sp K) i) ->
       regs_ok (ENV vals1) sn_sr2 R2 -> know_ok RSEGS (ENV vals1) M1 kn1 -> frame_mod mem M1 (sn_regions_w sp) ->
       lzok RSEGS L S Zr (mkCfg msF2 mo2) -> same_but_materialized mo mo2 -> hid_same L S msF msF2 ->
       restrict L S msF2 = mkst R2 (Z_to_bv 64 0x1ab16c) M1 (seg_rom RSEGS) -> realizes RSEGS (mkCfg msF2 mo2) KX) ->
    realizes RSEGS (mkCfg msF mo) KX.
  Proof.
    intros knX r1 c1 kn1 regs mem msF mo sp s ra K buf KX EX EC PC1 SC1 CC1 SR1 KN1 COV1 KV1 PH HK OK RS HCONT.
    pose proof (sn_regs_ok regs mem sp s ra K buf PH) as HR. pose proof PH as PH0.
    destruct PH as [G1 G2 G10 G11 Hsp16 HspLo HspHi Hstk Himg Hgot Hac Hinv Hmc HsLo HsHi Hdisj Hsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs. pose proof (HK0 _ _ _ _ _ Hmc) as K0. pose proof (HKn _ _ _ _ _ Hmc) as Kn.
    unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI in *.
    set (vals := sn_vals regs sp K) in *.
    assert (HL : length vals = 34%nat) by (subst vals; unfold sn_vals; rewrite length_app, junk_vals_length; reflexivity).
    assert (P0 : vals_ev vals 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals 1 = Z_to_bv 64 K) by reflexivity.
    assert (P12 : vals_ev vals 12 = s) by (subst vals; etransitivity; [exact (sn_ev_junk regs sp K 12 ltac:(lia)) | exact G10]).
    pose proof (sn_regions_flat vals sp P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (sn_regions_denot vals sp P0 ltac:(unfold ASP_LO; lia)) as RD.
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELN STOPSN scr0 0x1a86fc sn_sr knX 34 (fst (fst r1)) (snd (fst r1)) (snd r1)
              (fst (fst c1)) (snd (fst c1)) (snd c1) (ENV vals) mem (seg_rom RSEGS) regs msF mo);
      [ destruct r1 as [[? ?] ?]; cbn [fst snd]; exact EX | destruct c1 as [[? ?] ?]; cbn [fst snd]; exact EC
      | exact HR | exact HK | rewrite SC1; constructor | rewrite CC1; constructor | exact OK | exact RS | ].
    clear HR HK. intros R1 M1 msF1 mo1 HR HK EQ1 LF1 OK1 SB1 HS1 RS1.
    pose proof (log_covered_frame (ENV vals) mem sn_regions _ COV1 RF LF1) as F1. rewrite <- EQ1, RD in F1.
    rewrite SR1 in HR. rewrite KN1 in HK. rewrite PC1 in RS1.
    destruct (sn_mem_frame regs mem sp s ra K buf M1 PH0 F1) as (ST1 & INV1 & AC1 & MC1 & SH1).
    (* [comment removed for export] *)
    lazymatch type of RS1 with restrict _ _ _ = mkst ?Rc _ _ _ =>
      assert (A1 : getr Rc 1 = (0x1ab16c%bv : word)) by (regv HR (1%bv : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = s) by (regv HR (10%bv : reg); cbn [edenot ev ENV]; exact P12);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0) by (regv HR (11%bv : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 2147483647) by (regv HR (12%bv : reg); reflexivity);
      destruct (ref_memchr0 M1 s buf K 2147483647 (seg_rom RSEGS) Rc (0x1ab16c%bv : word) MC1
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep & Ha0);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 AMEMCHR) with (0x5698e0%bv : word) in RS1 by (apply bv_eq; reflexivity).
    eapply (rz_msteps_lazy_mkst RSEGS L S Zr); [exact OK1 | exact RS1 | exact Hms |]. clear Hms RS1.
    intros msF2 mo2 OK2 SB2 HS2 RS2.
    replace (0x1ab16c%bv : word) with (Z_to_bv 64 0x1ab16c) in RS2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    pose proof (regs_after_keeps vals (blobs_ev []) sn_sr1 _ R2 callee_saved ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_saved_no0) as HRj.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) M1 kn1 ltac:(rewrite HL; exact KV1) HK) as HK1.
    rewrite HL in HRj. clear HR HK.
    assert (HL1 : length (vals ++ junk_vals R2) = 66%nat) by (rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (QV : forall i, (i < 34)%nat -> vals_ev (vals ++ junk_vals R2) i = vals_ev vals i) by (intros i Hi; apply vals_ev_app_l; rewrite HL; exact Hi).
    apply (HCONT R2 M1 msF2 mo2 (vals ++ junk_vals R2) HL1 QV); try assumption.
    - intros r. destruct (bv_eq_dec 5 r 10%bv) as [->|NE].
      + rewrite Ha0. change (sr_get sn_sr2 10%bv) with (EAlu ALU_ADD (EVar 12) (EVar 1)). cbn [edenot ev ENV]. rewrite !QV by lia. rewrite P12, P1.
        cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite (Z.mod_small K) by lia. reflexivity.
      + rewrite (HRj r). destruct (reg_of_nat r) as (n & -> & Hn).
        do 32 (destruct n as [|n]; [first [reflexivity | exfalso; apply NE; apply bv_eq; reflexivity] |]). lia.
    - eapply same_but_materialized_trans; [exact SB1 | exact SB2].
    - eapply hid_same_trans; [exact HS1 | exact HS2].
  Qed.

  (* [comment removed for export] *)
  Definition rip_kept : list reg := [1; 2; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
  Lemma rip_kept_no0 : ~ In (0%bv : reg) rip_kept.
  Proof. cbn [In rip_kept]. intros Hin. repeat (destruct Hin as [Hin|Hin]; [apply (f_equal bv_unsigned) in Hin; cbn in Hin; discriminate Hin|]). exact Hin. Qed.

  (* [comment removed for export] *)
  Ltac regs_after_rip HR vals HL Rn srn HRn :=
    let HRj := fresh "HRj" in
    lazymatch type of HR with regs_ok _ ?sr ?R0 =>
      pose proof (regs_after_keeps vals (blobs_ev []) sr R0 Rn rip_kept ltac:(rewrite HL; vm_compute; reflexivity) HR) as HRj end;
    lazymatch type of HRj with ?KE -> ?N0 -> _ =>
      assert (KEPT : KE) by (intros r Hr; cbn [In rip_kept] in Hr;
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]]]]]]]; reflexivity);
      specialize (HRj KEPT rip_kept_no0); clear KEPT
    end;
    rewrite HL in HRj;
    change (Env (vals_ev (vals ++ junk_vals Rn)) (blobs_ev [])) with (ENV (vals ++ junk_vals Rn)) in HRj;
    assert (HRn : regs_ok (ENV (vals ++ junk_vals Rn)) srn Rn);
    [ intros r; destruct (bv_eq_dec 5 r 10%bv) as [->|NE];
      [ reflexivity
      | rewrite (HRj r); destruct (reg_of_nat r) as (n & -> & Hn);
        do 32 (destruct n as [|n]; [first [reflexivity | exfalso; apply NE; apply bv_eq; reflexivity] |]); lia ]
    | clear HRj ].

  Theorem as_strnlen_k : forall regs mem msF mo (sp s ra : word) (K : Z) buf (KX : TSet),
    snH regs mem sp s ra K buf ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0x1a86fc) mem (seg_rom RSEGS) ->
    (forall regs' mem' msF' mo', snPost regs mem sp ra K regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 SN_RET) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) KX.
  Proof.
    intros regs mem msF mo sp s ra K buf KX PH OK RS HCONT. pose proof PH as PH0.
    destruct PH as [G1 G2 G10 G11 Hsp16 HspLo HspHi Hstk Himg Hgot Hac Hinv Hmc HsLo HsHi Hdisj Hsh0].
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs. pose proof (HK0 _ _ _ _ _ Hmc) as K0. pose proof (HKn _ _ _ _ _ Hmc) as Kn.
    unfold ASP_LO, ASP_HI, AHI_LO, AAPP_HI, KMAXS in *.
    pose proof sn_itinerary as (PC1q & SC1q & CC1q & SR1q & PC1s & SC1s & CC1s & SR1s & PC2q & SC2q & CC2q & PC2s & SC2s & CC2s
                                & PC3s & SC3s & CC3s & PC4s & SC4s & CC4s).
    assert (POST : forall R3 M3 msF3 mo3,
      getr R3 2 = sp -> getr R3 1 = ra -> getr R3 10 = Z_to_bv 64 K ->
      (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R3 r = getr regs r) ->
      frame_mod mem M3 (sn_regions_w sp) ->
      lzok RSEGS L S Zr (mkCfg msF3 mo3) -> same_but_materialized mo mo3 -> hid_same L S msF msF3 ->
      restrict L S msF3 = mkst R3 (Z_to_bv 64 SN_RET) M3 (seg_rom RSEGS) ->
      realizes RSEGS (mkCfg msF3 mo3) KX).
    { intros R3 M3 msF3 mo3 X2 X1 X10 XCS F OK3 SB3 HS3 RS3.
      destruct (sn_mem_frame regs mem sp s ra K buf M3 PH0 F) as (ST3 & INV3 & AC3 & _ & _).
      apply (HCONT R3 M3 msF3 mo3); try assumption. split; assumption. }
    (* [comment removed for export] *)
    assert (POSTR : forall (vals1 : list word) R3 srX,
      (forall i, (i < 34)%nat -> vals_ev vals1 i = vals_ev (sn_vals regs sp K) i) ->
      regs_ok (ENV vals1) srX R3 -> (srX = sn_srF \/ srX = sn_sr4s) ->
      getr R3 2 = sp /\ getr R3 1 = ra /\ getr R3 10 = Z_to_bv 64 K /\
      (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R3 r = getr regs r)).
    { intros vals1 R3 srX QV HR HX.
      assert (QJ : forall i, (2 <= i < 34)%nat -> vals_ev vals1 i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
      { intros i Hi. rewrite QV by lia. apply (sn_ev_junk regs sp K i Hi). }
      destruct HX as [-> | ->]; (split; [|split; [|split]]);
        [ regv HR (2%bv : reg); cbn [edenot ev ENV]; rewrite QV by lia; reflexivity
        | regv HR (1%bv : reg); cbn [edenot ev ENV]; rewrite QJ by lia; exact G1
        | regv HR (10%bv : reg); cbn [edenot ev ENV]; rewrite QV by lia; reflexivity
        | intros r Hr; cbn [In] in Hr;
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
          lazymatch goal with |- getr R3 ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite QJ by lia; f_equal; apply bv_eq; reflexivity
        | regv HR (2%bv : reg); cbn [edenot ev ENV]; rewrite QV by lia; reflexivity
        | regv HR (1%bv : reg); cbn [edenot ev ENV]; rewrite QJ by lia; exact G1
        | regv HR (10%bv : reg); cbn [edenot ev ENV]; rewrite QV by lia; reflexivity
        | intros r Hr; cbn [In] in Hr;
          destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
          lazymatch goal with |- getr R3 ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite QJ by lia; f_equal; apply bv_eq; reflexivity ]. }
    destruct (Z_lt_le_dec K 64) as [KQ|KS].
    - (* [comment removed for export] *)
      pose proof (sn_know_ok regs mem sp s ra K buf 0 63 PH0 ltac:(lia) ltac:(lia)) as HK. change (sn_kn 0 63) with sn_knQ in HK.
      apply (sn_head sn_knQ sn_r1q sn_c1q sn_kn1q regs mem msF mo sp s ra K buf KX
               ltac:(vm_cast_no_check (@eq_refl _ sn_r1q)) ltac:(vm_cast_no_check (@eq_refl _ sn_c1q))
               PC1q SC1q CC1q SR1q eq_refl sn_cov1q ltac:(vm_compute; reflexivity) PH0 HK OK RS).
      clear HK OK RS. intros R2 M1 msF2 mo2 vals1 HL1 QV HR2 HK1 F1 OK2 SB2 HS2 RS2.
      assert (Q0 : vals_ev vals1 0 = sp) by (rewrite QV by lia; reflexivity).
      assert (Q1 : vals_ev vals1 1 = Z_to_bv 64 K) by (rewrite QV by lia; reflexivity).
      assert (Q12 : vals_ev vals1 12 = s) by (rewrite QV by lia; etransitivity; [exact (sn_ev_junk regs sp K 12 ltac:(lia)) | exact G10]).
      pose proof (sn_regions_flat vals1 sp Q0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF1.
      pose proof (sn_regions_denot vals1 sp Q0 ltac:(unfold ASP_LO; lia)) as RD1.
      (* [comment removed for export] *)
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELN STOPSN scrQ 0x1ab16c sn_sr2 sn_kn1q 66 (fst (fst sn_r2q)) (snd (fst sn_r2q)) (snd sn_r2q)
                (fst (fst sn_c2q)) (snd (fst sn_c2q)) (snd sn_c2q) (ENV vals1) M1 (seg_rom RSEGS) R2 msF2 mo2);
        [ vm_cast_no_check (@eq_refl _ sn_r2q) | vm_cast_no_check (@eq_refl _ sn_c2q)
        | exact HR2 | exact HK1
        | rewrite SC2q; apply (sn_scs_ok vals1 M1 s K); [exact Q12 | exact Q1 | unfold AHI_LO; lia | unfold AAPP_HI; lia | lia | cbn; tauto]
        | rewrite CC2q; constructor | exact OK2 | exact RS2 | ].
      clear HR2 HK1. intros R3 M3 msF3 mo3 HR HK EQ3 LF3 OK3 SB3 HS3 RS3.
      pose proof (log_covered_frame (ENV vals1) M1 sn_regions _ sn_cov2q RF1 LF3) as F3. rewrite <- EQ3, RD1 in F3.
      change (s_regs (fst (fst sn_r2q))) with sn_srF in HR. rewrite PC2q in RS3.
      destruct (POSTR vals1 R3 sn_srF QV HR ltac:(left; reflexivity)) as (X2 & X1 & X10 & XCS).
      apply (POST R3 M3 msF3 mo3 X2 X1 X10 XCS); try assumption.
      + eapply frame_mod_trans_same; [exact F1 | exact F3].
      + eapply same_but_materialized_trans; [exact SB2 | exact SB3].
      + eapply hid_same_trans; [exact HS2 | exact HS3].
    - (* [comment removed for export] *)
      pose proof (sn_know_ok regs mem sp s ra K buf 64 (2^31 - 9) PH0 ltac:(lia) ltac:(lia)) as HK. change (sn_kn 64 (2^31 - 9)) with sn_knS in HK.
      apply (sn_head sn_knS sn_r1s sn_c1s sn_kn1s regs mem msF mo sp s ra K buf KX
               ltac:(vm_cast_no_check (@eq_refl _ sn_r1s)) ltac:(vm_cast_no_check (@eq_refl _ sn_c1s))
               PC1s SC1s CC1s SR1s eq_refl sn_cov1s ltac:(vm_compute; reflexivity) PH0 HK OK RS).
      clear HK OK RS. intros R2 M1 msF2 mo2 vals1 HL1 QV HR2 HK1 F1 OK2 SB2 HS2 RS2.
      assert (Q0 : vals_ev vals1 0 = sp) by (rewrite QV by lia; reflexivity).
      assert (Q1 : vals_ev vals1 1 = Z_to_bv 64 K) by (rewrite QV by lia; reflexivity).
      assert (Q12 : vals_ev vals1 12 = s) by (rewrite QV by lia; etransitivity; [exact (sn_ev_junk regs sp K 12 ltac:(lia)) | exact G10]).
      pose proof (sn_regions_flat vals1 sp Q0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF1.
      pose proof (sn_regions_denot vals1 sp Q0 ltac:(unfold ASP_LO; lia)) as RD1.
      (* [comment removed for export] *)
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELN STOPSN scrS 0x1ab16c sn_sr2 sn_kn1s 66 (fst (fst sn_r2s)) (snd (fst sn_r2s)) (snd sn_r2s)
                (fst (fst sn_c2s)) (snd (fst sn_c2s)) (snd sn_c2s) (ENV vals1) M1 (seg_rom RSEGS) R2 msF2 mo2);
        [ vm_cast_no_check (@eq_refl _ sn_r2s) | vm_cast_no_check (@eq_refl _ sn_c2s)
        | exact HR2 | exact HK1
        | rewrite SC2s; apply (sn_scs_ok vals1 M1 s K); [exact Q12 | exact Q1 | unfold AHI_LO; lia | unfold AAPP_HI; lia | lia | cbn; tauto]
        | rewrite CC2s; constructor | exact OK2 | exact RS2 | ].
      clear HR2 HK1. intros R2S M2 msF2S mo2S HR HK EQ2 LF2 OK2S SB2S HS2S RS2S.
      pose proof (log_covered_frame (ENV vals1) M1 sn_regions _ sn_cov2s RF1 LF2) as F2. rewrite <- EQ2, RD1 in F2.
      change (s_regs (fst (fst sn_r2s))) with sn_sr2s in HR. change (fst (fst sn_c2s)) with sn_kn2s in HK. rewrite PC2s in RS2S.
      assert (F12 : frame_mod mem M2 (sn_regions_w sp)) by (eapply frame_mod_trans_same; [exact F1 | exact F2]).
      destruct (sn_mem_frame regs mem sp s ra K buf M2 PH0 F12) as (ST2 & INV2 & AC2 & _ & SH2).
      (* [comment removed for export] *)
      assert (U1 : getr R2S 1%bv = Z_to_bv 64 0x1ab304) by (regv HR (1%bv : reg); reflexivity).
      assert (U2 : bv_unsigned (getr R2S 2%bv) = bv_unsigned sp - 4304).
      { regv HR (2%bv : reg). cbn [edenot ev ENV]. rewrite Q0, alu_add, vadd_wZ. unorm. lia. }
      assert (U10 : getr R2S 10%bv = s) by (regv HR (10%bv : reg); cbn [edenot ev ENV]; exact Q12).
      assert (U11 : bv_unsigned (getr R2S 11%bv) = K + 1).
      { regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite Q1, alu_add, vadd_wZ. unorm. lia. }
      unfold getr in U1, U2, U10, U11. change (bv_eqb 1%bv 0%bv) with false in U1. change (bv_eqb 2%bv 0%bv) with false in U2.
      change (bv_eqb 10%bv 0%bv) with false in U10. change (bv_eqb 11%bv 0%bv) with false in U11. cbv iota in U1, U2, U10, U11.
      apply (lz_renorm msF2S mo2S R2S _ M2 _ KX OK2S RS2S). intros msFn OKn RSn HSn.
      apply (lz_evt (rip_post (reg_get R2S 1) (reg_get R2S 2) (reg_get R2S 3) (reg_get R2S 4) (reg_get R2S 6) (reg_get R2S 7)
                       (reg_get R2S 8) (reg_get R2S 9) (reg_get R2S 18) (reg_get R2S 19) (reg_get R2S 20) (reg_get R2S 21)
                       (reg_get R2S 22) (reg_get R2S 23) (reg_get R2S 24) (reg_get R2S 25) (reg_get R2S 26) (reg_get R2S 27)
                       (reg_get R2S 28) (reg_get R2S 29) (reg_get R2S 30) (reg_get R2S 31) bvmap_empty (Z_to_bv 32 0)
                       (bv_unsigned sp - SN_FR) M2) msFn mo2S KX OKn).
      { rewrite RSn. unfold mkR_of. change (Z_to_bv 64 ARIP) with (Z_to_bv 64 rip_entry).
        apply rip_body_w.
        - exact INV2.
        - exact AC2.
        - rewrite U10, U11. apply accessible_of_sh0; [| unfold AHI_LO; lia | unfold AAPP_HI; lia | lia].
          intros a Ha. apply SH2. replace (bv_unsigned s + (K + 1) - 1) with (bv_unsigned s + K) in Ha by lia. exact Ha.
        - rewrite U11. lia.
        - rewrite U10, U11. right. unfold AHI_LO, AAPP_HI. lia.
        - rewrite U2. exact (proj1 (stk_split asegs M2 _ (bv_unsigned sp - 4304) _ ST2 ltac:(unfold SN_FR; lia))).
        - rewrite U2. unfold RIP_STACK, SN_FR. lia.
        - unfold AHI_LO, SN_FR. lia. }
      clear OKn RSn. intros msF3 mo3 OK3 SB3 HS3 HP3.
      destruct HP3 as (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m3 & RS3 & MU3 & WM3 & INV3 & ST3 & AC3).
      assert (RP : ret_pc (reg_get R2S 1) = Z_to_bv 64 0x1ab304) by (rewrite U1; apply ret_pc_even; [lia | reflexivity]).
      rewrite RP in RS3. clear RP. rewrite U2 in MU3, ST3.
      lazymatch type of RS3 with _ = MS ?Rx _ ?pcx _ _ _ ?romx =>
        change (restrict L S msF3 = mkst Rx pcx m3 romx) in RS3; set (R3 := Rx) in RS3 end.
      assert (G23 : mem_grows M2 m3).
      { eapply (mem_grows_of_stk M2 m3 _ _ (bv_unsigned sp - SN_FR) (bv_unsigned sp - 4304) MU3 ST3); unfold SN_FR; lia. }
      assert (F23 : frame_mod M2 m3 (sn_regions_w sp)) by (eapply frame_mod_of_munch; [exact MU3 | exact G23 | unfold SN_FR; lia | lia | unfold SN_FR; lia]).
      assert (F13 : frame_mod mem m3 (sn_regions_w sp)) by (eapply frame_mod_trans_same; [exact F12 | exact F23]).
      (* [comment removed for export] *)
      pose proof (know_cut_sound RSEGS (ENV vals1) M2 m3 0 (-4384) (-4304) 0xc04000 sn_kn2s
                    ltac:(unfold win_ok; cbn [ev ENV]; rewrite Q0; lia)
                    ltac:(intros x Hx; apply MU3; cbn [outside]; cbn [ev ENV] in Hx; rewrite Q0 in Hx; split; [lia | exact I])
                    G23 HK) as HK3.
      change (kn_cut 0 (-4384) (-4304) 0xc04000 sn_kn2s) with sn_kn3e in HK3. clear HK.
      pose proof (env_app_know RSEGS vals1 (junk_vals R3) (blobs_ev []) m3 sn_kn3e ltac:(rewrite HL1; vm_compute; reflexivity) HK3) as HK3'.
      clear HK3. change (Env (vals_ev (vals1 ++ junk_vals R3)) (blobs_ev [])) with (ENV (vals1 ++ junk_vals R3)) in HK3'.
      regs_after_rip HR vals1 HL1 R3 sn_sr3 HR3. clear HR.
      set (vals2 := vals1 ++ junk_vals R3) in *.
      assert (HL2 : length vals2 = 98%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL1; reflexivity).
      assert (QV2 : forall i, (i < 34)%nat -> vals_ev vals2 i = vals_ev (sn_vals regs sp K) i).
      { intros i Hi. subst vals2. rewrite vals_ev_app_l by (rewrite HL1; lia). apply QV. exact Hi. }
      assert (W0 : vals_ev vals2 0 = sp) by (rewrite QV2 by lia; reflexivity).
      assert (W1 : vals_ev vals2 1 = Z_to_bv 64 K) by (rewrite QV2 by lia; reflexivity).
      assert (W12 : vals_ev vals2 12 = s) by (rewrite QV2 by lia; etransitivity; [exact (sn_ev_junk regs sp K 12 ltac:(lia)) | exact G10]).
      clearbody vals2. clear Q0 Q1 Q12 QV RF1 RD1 U1 U2 U10 U11.
      pose proof (sn_regions_flat vals2 sp W0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF2.
      pose proof (sn_regions_denot vals2 sp W0 ltac:(unfold ASP_LO; lia)) as RD2.
      (* [comment removed for export] *)
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELN STOPSN (SCR [false] [] []) 0x1ab304 sn_sr3 sn_kn3e 98 (fst (fst sn_r3s)) (snd (fst sn_r3s)) (snd sn_r3s)
                (fst (fst sn_c3s)) (snd (fst sn_c3s)) (snd sn_c3s) (ENV vals2) m3 (seg_rom RSEGS) R3 msF3 mo3);
        [ vm_cast_no_check (@eq_refl _ sn_r3s) | vm_cast_no_check (@eq_refl _ sn_c3s)
        | exact HR3 | exact HK3'
        | rewrite SC3s; apply (sn_scs_ok vals2 m3 s K); [exact W12 | exact W1 | unfold AHI_LO; lia | unfold AAPP_HI; lia | lia | cbn; tauto]
        | rewrite CC3s; constructor | exact OK3 | exact RS3 | ].
      clear HR3 HK3'. intros R3S M4 msF3S mo3S HR HK EQ4 LF4 OK3S SB3S HS3S RS3S.
      pose proof (log_covered_frame (ENV vals2) m3 sn_regions _ sn_cov3s RF2 LF4) as F34. rewrite <- EQ4, RD2 in F34.
      change (s_regs (fst (fst sn_r3s))) with sn_sr3s in HR. change (fst (fst sn_c3s)) with sn_kn3s in HK. rewrite PC3s in RS3S.
      assert (F14 : frame_mod mem M4 (sn_regions_w sp)) by (eapply frame_mod_trans_same; [exact F13 | exact F34]).
      destruct (sn_mem_frame regs mem sp s ra K buf M4 PH0 F14) as (ST4 & INV4 & AC4 & _ & SH4).
      (* [comment removed for export] *)
      assert (U1 : getr R3S 1%bv = Z_to_bv 64 0x1a8c4c) by (regv HR (1%bv : reg); reflexivity).
      assert (U2 : bv_unsigned (getr R3S 2%bv) = bv_unsigned sp - 2144).
      { regv HR (2%bv : reg). cbn [edenot ev ENV]. rewrite W0, alu_add, vadd_wZ. unorm. lia. }
      assert (U10 : getr R3S 10%bv = s) by (regv HR (10%bv : reg); cbn [edenot ev ENV]; exact W12).
      assert (U11 : bv_unsigned (getr R3S 11%bv) = K + 1).
      { regv HR (11%bv : reg). cbn [edenot ev ENV]. rewrite W1, alu_add, vadd_wZ. unorm. lia. }
      unfold getr in U1, U2, U10, U11. change (bv_eqb 1%bv 0%bv) with false in U1. change (bv_eqb 2%bv 0%bv) with false in U2.
      change (bv_eqb 10%bv 0%bv) with false in U10. change (bv_eqb 11%bv 0%bv) with false in U11. cbv iota in U1, U2, U10, U11.
      apply (lz_renorm msF3S mo3S R3S _ M4 _ KX OK3S RS3S). intros msFn2 OKm RSm HSm.
      apply (lz_evt (rip_post (reg_get R3S 1) (reg_get R3S 2) (reg_get R3S 3) (reg_get R3S 4) (reg_get R3S 6) (reg_get R3S 7)
                       (reg_get R3S 8) (reg_get R3S 9) (reg_get R3S 18) (reg_get R3S 19) (reg_get R3S 20) (reg_get R3S 21)
                       (reg_get R3S 22) (reg_get R3S 23) (reg_get R3S 24) (reg_get R3S 25) (reg_get R3S 26) (reg_get R3S 27)
                       (reg_get R3S 28) (reg_get R3S 29) (reg_get R3S 30) (reg_get R3S 31) bvmap_empty (Z_to_bv 32 0)
                       (bv_unsigned sp - SN_FR) M4) msFn2 mo3S KX OKm).
      { rewrite RSm. unfold mkR_of. change (Z_to_bv 64 ARIP) with (Z_to_bv 64 rip_entry).
        apply rip_body_w.
        - exact INV4.
        - exact AC4.
        - rewrite U10, U11. apply accessible_of_sh0; [| unfold AHI_LO; lia | unfold AAPP_HI; lia | lia].
          intros a Ha. apply SH4. replace (bv_unsigned s + (K + 1) - 1) with (bv_unsigned s + K) in Ha by lia. exact Ha.
        - rewrite U11. lia.
        - rewrite U10, U11. right. unfold AHI_LO, AAPP_HI. lia.
        - rewrite U2. exact (proj1 (stk_split asegs M4 _ (bv_unsigned sp - 2144) _ ST4 ltac:(unfold SN_FR; lia))).
        - rewrite U2. unfold RIP_STACK, SN_FR. lia.
        - unfold AHI_LO, SN_FR. lia. }
      clear OKm RSm. intros msF4 mo4 OK4 SB4 HS4 HP4.
      destruct HP4 as (t0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & m4 & RS4 & MU4 & WM4 & INV4' & ST4' & AC4').
      assert (RP : ret_pc (reg_get R3S 1) = Z_to_bv 64 0x1a8c4c) by (rewrite U1; apply ret_pc_even; [lia | reflexivity]).
      rewrite RP in RS4. clear RP. rewrite U2 in MU4, ST4'.
      lazymatch type of RS4 with _ = MS ?Rx _ ?pcx _ _ _ ?romx =>
        change (restrict L S msF4 = mkst Rx pcx m4 romx) in RS4; set (R4 := Rx) in RS4 end.
      assert (G45 : mem_grows M4 m4).
      { eapply (mem_grows_of_stk M4 m4 _ _ (bv_unsigned sp - SN_FR) (bv_unsigned sp - 2144) MU4 ST4'); unfold SN_FR; lia. }
      assert (F45 : frame_mod M4 m4 (sn_regions_w sp)) by (eapply frame_mod_of_munch; [exact MU4 | exact G45 | unfold SN_FR; lia | lia | unfold SN_FR; lia]).
      assert (F15 : frame_mod mem m4 (sn_regions_w sp)) by (eapply frame_mod_trans_same; [exact F14 | exact F45]).
      pose proof (know_cut_sound RSEGS (ENV vals2) M4 m4 0 (-2224) (-2144) 0xc04000 sn_kn3s
                    ltac:(unfold win_ok; cbn [ev ENV]; rewrite W0; lia)
                    ltac:(intros x Hx; apply MU4; cbn [outside]; cbn [ev ENV] in Hx; rewrite W0 in Hx; split; [lia | exact I])
                    G45 HK) as HK4.
      change (kn_cut 0 (-2224) (-2144) 0xc04000 sn_kn3s) with sn_kn4e in HK4. clear HK.
      pose proof (env_app_know RSEGS vals2 (junk_vals R4) (blobs_ev []) m4 sn_kn4e ltac:(rewrite HL2; vm_compute; reflexivity) HK4) as HK4'.
      clear HK4. change (Env (vals_ev (vals2 ++ junk_vals R4)) (blobs_ev [])) with (ENV (vals2 ++ junk_vals R4)) in HK4'.
      regs_after_rip HR vals2 HL2 R4 sn_sr4 HR4. clear HR.
      set (vals3 := vals2 ++ junk_vals R4) in *.
      assert (HL3 : length vals3 = 130%nat) by (subst vals3; rewrite length_app, junk_vals_length, HL2; reflexivity).
      assert (QV3 : forall i, (i < 34)%nat -> vals_ev vals3 i = vals_ev (sn_vals regs sp K) i).
      { intros i Hi. subst vals3. rewrite vals_ev_app_l by (rewrite HL2; lia). apply QV2. exact Hi. }
      assert (X0 : vals_ev vals3 0 = sp) by (rewrite QV3 by lia; reflexivity).
      clearbody vals3. clear W0 W1 W12 QV2 RF2 RD2 U1 U2 U10 U11.
      pose proof (sn_regions_flat vals3 sp X0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF3.
      pose proof (sn_regions_denot vals3 sp X0 ltac:(unfold ASP_LO; lia)) as RD3.
      (* [comment removed for export] *)
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELN STOPSN scr0 0x1a8c4c sn_sr4 sn_kn4e 130 (fst (fst sn_r4s)) (snd (fst sn_r4s)) (snd sn_r4s)
                (fst (fst sn_c4s)) (snd (fst sn_c4s)) (snd sn_c4s) (ENV vals3) m4 (seg_rom RSEGS) R4 msF4 mo4);
        [ vm_cast_no_check (@eq_refl _ sn_r4s) | vm_cast_no_check (@eq_refl _ sn_c4s)
        | exact HR4 | exact HK4'
        | rewrite SC4s; constructor | rewrite CC4s; constructor | exact OK4 | exact RS4 | ].
      clear HR4 HK4'. intros R5 M5 msF5 mo5 HR HK EQ5 LF5 OK5 SB5 HS5 RS5.
      pose proof (log_covered_frame (ENV vals3) m4 sn_regions _ sn_cov4s RF3 LF5) as F56. rewrite <- EQ5, RD3 in F56.
      change (s_regs (fst (fst sn_r4s))) with sn_sr4s in HR. rewrite PC4s in RS5.
      destruct (POSTR vals3 R5 sn_sr4s QV3 HR ltac:(right; reflexivity)) as (X2 & X1 & X10 & XCS).
      apply (POST R5 M5 msF5 mo5 X2 X1 X10 XCS); try assumption.
      + eapply frame_mod_trans_same; [exact F15 | exact F56].
      + eapply same_but_materialized_trans; [exact SB2|]. eapply same_but_materialized_trans; [exact SB2S|].
        eapply same_but_materialized_trans; [exact SB3|]. eapply same_but_materialized_trans; [exact SB3S|].
        eapply same_but_materialized_trans; [exact SB4 | exact SB5].
      + eapply hid_same_trans; [exact HS2|]. eapply hid_same_trans; [exact HS2S|]. eapply hid_same_trans; [exact HSn |].
        eapply hid_same_trans; [exact HS3|]. eapply hid_same_trans; [exact HS3S|]. eapply hid_same_trans; [exact HSm |].
        eapply hid_same_trans; [exact HS4 | exact HS5].
  Qed.
End Plain.
