(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg L5Defs L5Core FrmInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PD.
Definition is_dig (c : Z) : bool := (48 <=? c) && (c <=? 57).
(* [comment removed for export] *)
Fixpoint span (p : Z -> bool) (l : list Z) : Z * list Z :=
  match l with
  | c :: r => if p c then let '(n, r') := span p r in (n + 1, r') else (0, l)
  | [] => (0, l)
  end.
(* [comment removed for export] *)
Definition exp_scan (l : list Z) : option Z :=
  let '(sg, r) := match l with c :: r' => if (c =? 43) || (c =? 45) then (1, r') else (0, l) | [] => (0, l) end in
  let '(n, _) := span is_dig r in
  if n =? 0 then None else Some (sg + n).
(* [comment removed for export] *)
Fixpoint dig_loop (gotrad : bool) (l : list Z) : Z * bool * list Z :=
  match l with
  | c :: r =>
      if is_dig c then let '(n, _, r') := dig_loop gotrad r in (n + 1, true, r')
      else if (c =? 46) && negb gotrad then let '(n, d, r') := dig_loop true r in (n + 1, d, r')
      else (0, false, l)
  | [] => (0, false, l)
  end.
(* [comment removed for export] *)
Definition dec_len (l : list Z) : Z :=
  let '(n1, r1) := span (fun c => c =? 48) l in
  let '(nd, gotrad, n2, r2) :=
      match r1 with
      | 46 :: r' => let '(n2, r2) := span (fun c => c =? 48) r' in (1, true, n2, r2)
      | _ => (0, false, 0, r1)
      end in
  let '(n3, d3, r3) := dig_loop gotrad r2 in
  let gotdig := (0 <? n1) || (0 <? n2) || d3 in
  let ne := match r3 with
            | c :: r' => if gotdig && ((c =? 101) || (c =? 69)) then match exp_scan r' with Some k => 1 + k | None => 0 end else 0
            | [] => 0
            end in
  n1 + nd + n2 + n3 + ne.

(* [comment removed for export] *)
Example ex1 : dec_len [49; 50; 51] = 3. Proof. reflexivity. Qed.
Example ex2 : dec_len [48; 46; 53; 48; 101; 43; 49; 48] = 8. Proof. reflexivity. Qed.
Example ex3 : dec_len [49; 101] = 1. Proof. reflexivity. Qed.
Example ex4 : dec_len [49; 46; 101; 53; 120] = 4. Proof. reflexivity. Qed.
Example ex5 : dec_len [48; 120] = 1. Proof. reflexivity. Qed.
Example ex6 : dec_len [49; 46; 50; 46; 51] = 3. Proof. reflexivity. Qed.
End PD.

(* [comment removed for export] *)
(* [comment removed for export] *)
Module PDC.
Record addrs : Type := ADDRS { a_E1 : Z; a_E2 : Z; a_scanexp : Z; a_G : Z (* [comment removed for export] *); a_TP : Z (* [comment removed for export] *);
                               a_img_lo : Z; a_img_hi : Z (* [comment removed for export] *) }.
Definition src11 : addrs := ADDRS 0xb9234 0xb9384 0xbad40 0xfd280 0xdd010 0x10000 0xca250.
Definition SCR_D : Z := 256.            (* [comment removed for export] *)
Definition FRAME : Z := 8416.           (* [comment removed for export] *)
Definition STK_FLOOR : Z := 140735332483072.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SAVES : list (nat * Z) :=
  [(1%nat, 2024); (8%nat, 2016); (9%nat, 2008); (18%nat, 2000); (19%nat, 1992); (20%nat, 1984); (21%nat, 1976); (22%nat, 1968); (23%nat, 1960); (24%nat, 1952);
   (25%nat, 1944); (26%nat, 1936); (27%nat, 1928)].
Definition reg_of (n : nat) : reg := Z_to_bv 5 (Z.of_nat n).
Definition rz (R : bvmap 5 word) (n : nat) : Z := bv_unsigned (getr R (reg_of n)).
Definition apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.

Section Contracts.
Variable segs : list Segment.
Context {SCFG_P : ScfgP}.
Variable A : addrs.

(* [comment removed for export] *)
Definition file_ok (M : word -> option byte) (F P : Z) : Prop :=
  L5.u64_at segs M (F + 8) P /\ L5.u64_at segs M (F + 184) (2 ^ 64 - 1) /\ L5.u64_at segs M (F + 192) 0 /\ L5.writable segs M (F + 8) 8 /\
  STK_FLOOR <= F /\ F + 256 <= 2 ^ 47.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition text_ok (M : word -> option byte) (Q : Z) (txt : list Z) : Prop :=
  L5.bytes_at segs M Q txt /\ L5.u8_at segs M (Q + Z.of_nat (length txt)) 0 /\ 4096 <= Q /\ Q + Z.of_nat (length txt) < 2 ^ 47 /\ Z.of_nat (length txt) < 2 ^ 26 /\
  L5.defined M Q (Z.of_nat (length txt) + 1) /\ Forall (fun c => 0 <= c < 256) txt.
Definition text_apart (Q : Z) (txt : list Z) (F lo n : Z) : Prop :=
  let len := Z.of_nat (length txt) + 1 in apart Q len lo n /\ apart Q len (F + 8) 192 /\ apart Q len (a_TP A - 164) 4.

(* [comment removed for export] *)
Definition dec_pre (e2 : bool) (R : bvmap 5 word) (M : word -> option byte) (SP F P Q CAN : Z) (sv : nat -> Z) (txt : list Z) : Prop :=
  rz R 2 = SP /\ SP mod 16 = 0 /\ STK_FLOOR + SCR_D <= SP /\ SP + FRAME <= 2 ^ 47 /\
  rz R 21 = F /\ rz R 23 = 1 /\ rz R 18 = 53 /\ rz R 22 = 2 ^ 64 - 1074 /\ rz R 24 = 1 /\ (rz R 9 = 1 \/ rz R 9 = 2 ^ 64 - 1) /\ rz R 20 = a_G A /\ rz R 4 = a_TP A /\
  L5.defined M (SP - SCR_D) (SCR_D + FRAME) /\ L5.writable segs M (SP - SCR_D) (SCR_D + FRAME) /\
  (forall r o, In (r, o) SAVES -> L5.u64_at segs M (SP + 6384 + o) (sv r) /\ 0 <= sv r < 2 ^ 64) /\ Hoare.ret_ok (Z_to_bv 64 (sv 1%nat)) /\
  L5.u64_at segs M (SP + 8296) CAN /\ L5.u64_at segs M (a_G A) CAN /\ apart (a_G A) 8 (SP - SCR_D) (SCR_D + FRAME) /\
  file_ok M F P /\ apart (F + 8) 192 (SP - SCR_D) (SCR_D + FRAME) /\
  text_ok M Q txt /\ text_apart Q txt F (SP - SCR_D) (SCR_D + FRAME) /\
  L5.writable segs M (a_TP A - 164) 4 /\      (* [comment removed for export] *)
  L5.img_clear M (a_img_lo A) (a_img_hi A) /\
  (if e2 then Q = P - 2 /\ (exists r, txt = 48 :: r)
   else Q = P - 1 /\ (exists c r, txt = c :: r /\ 49 <= c <= 57 /\ rz R 10 = c)).
Definition dec_post (R : bvmap 5 word) (M : word -> option byte) (SP F Q : Z) (sv : nat -> Z) (txt : list Z) (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
  rz R' 2 = SP + FRAME /\ (forall r o, In (r, o) SAVES -> rz R' r = sv r) /\ getr R' (reg_of 3) = getr R (reg_of 3) /\ getr R' (reg_of 4) = getr R (reg_of 4) /\
  (forall a : word, ~ (SP - SCR_D <= bv_unsigned a < SP + FRAME) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> ~ (a_TP A - 164 <= bv_unsigned a < a_TP A - 160) -> M' a = M a) /\
  mem_grows M M' /\
  L5.u64_at segs M' (F + 8) (Q + PD.dec_len txt).
Definition decfloat_contract (e2 : bool) : Prop :=
  forall (fx : FPState) R M model K SP F P Q CAN sv txt,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx -> dec_pre e2 R M SP F P Q CAN sv txt ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' -> dec_post R M SP F Q sv txt R' M' ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (sv 1%nat)) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (if e2 then a_E2 A else a_E1 A)) M (seg_rom segs)) model) K.

(* [comment removed for export] *)
Definition scanexp_contract : Prop :=
  forall (fx : FPState) R M model K sp F P' txt,
  m_halted model = None -> m_vm_lazy model = [] -> FrmInv.fp_ok fx ->
  rz R 2 = sp -> sp mod 16 = 0 -> STK_FLOOR + 80 <= sp <= 2 ^ 47 -> L5.defined M (sp - 80) 80 -> L5.writable segs M (sp - 80) 80 ->
  rz R 10 = F -> rz R 11 = 1 -> Hoare.ret_ok (getr R (reg_of 1)) ->
  file_ok M F P' -> apart (F + 8) 192 (sp - 80) 80 -> text_ok M P' txt -> text_apart P' txt F (sp - 80) 80 ->
  L5.img_clear M (a_img_lo A) (a_img_hi A) ->
  (forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall a : word, ~ (sp - 80 <= bv_unsigned a < sp) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> M' a = M a) -> mem_grows M M' ->
      (forall x : nat, In x [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg_of x) = getr R (reg_of x)) ->
      match PD.exp_scan txt with
      | Some k => L5.u64_at segs M' (F + 8) (P' + k) /\ rz R' 10 <> 2 ^ 63
      | None => L5.u64_at segs M' (F + 8) P' /\ rz R' 10 = 2 ^ 63
      end ->
      srealizes segs SCFG (mkCfg (@mkst fx' R' (getr R (reg_of 1)) M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (a_scanexp A)) M (seg_rom segs)) model) K.
End Contracts.
End PDC.
