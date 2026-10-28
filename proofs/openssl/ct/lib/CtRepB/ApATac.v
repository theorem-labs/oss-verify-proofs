(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnBoth Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepB Require Import ApUTacB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithSegs.
Variable segs : list Segment.

Local Lemma bytes_at_munch1 : forall W m m1 A (b : byte),
  bytes_at segs m A [b] -> munch W m m1 -> offshW W -> SHLO <= A < SHHI -> bytes_at segs m1 A [b].
Proof.
  intros W m m1 A b Hb MU OFF R. eapply bytes_at_transport; [exact Hb | exact MU |]. cbn [length].
  assert (O : forall x, A <= x < A + Z.of_nat 1 -> outside W x) by (intros x Hx; apply offshW_outside; [exact OFF | lia]).
  clear - O. revert O. generalize A as B. induction W as [|[lo hi] W IH]; cbn; intros B O; [exact I|].
  split; [destruct (O B ltac:(lia)) as [O1 _]; lia | apply IH; intros x Hx; exact (proj2 (O x Hx))].
Qed.

(* [comment removed for export] *)
Lemma acc_rdG : forall W m m1 a n X ad,
  acc segs m a n -> munch W m m1 -> offshW W ->
  a <= X / 8 * 8 -> X / 8 * 8 + 8 <= a + n -> 0 <= a -> a + n <= 140737488355328 ->
  ad = wa (shad X) ->
  ov_read_bytes segs m1 ad 1 = Some [z8].
Proof.
  intros W m m1 a n X ad ACC MU OFF H1 H2 H0 HT ->.
  assert (Es : shad (X / 8 * 8) = shad X) by (unfold shad; f_equal; clear; Z.div_mod_to_equations; lia). rewrite <- Es.
  apply (acc_rd0 segs W m m1 a n (X / 8 * 8) _ ACC MU OFF); [clear; Z.div_mod_to_equations; lia | exact H1 | exact H2 | | reflexivity].
  clear - H1 H2 H0 HT. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition absh_ok (b : byte) (X s : Z) : Prop := b = z8 \/ (0 < bv_unsigned b < 8 /\ X mod 8 + s <= bv_unsigned b).

Lemma acc_rdS : forall W m m1 a n X s ad,
  acc segs m a n -> munch W m m1 -> offshW W ->
  a <= X -> X + s <= a + n -> 1 <= s -> 0 <= a -> a + n <= 140737488355328 ->
  ad = wa (shad X) ->
  exists b, ov_read_bytes segs m1 ad 1 = Some [b] /\ absh_ok b X s.
Proof.
  intros W m m1 a n X s ad ACC MU OFF H1 H2 Hs H0 HT ->.
  destruct (ACC (X - a) ltac:(lia)) as (b & Hb & Hok). replace (a + (X - a)) with X in * by lia.
  pose proof (shad_range X ltac:(lia)) as RS.
  exists b. split.
  - pose proof (bytes_at_read segs m1 (shad X) [b] 0 1 (bytes_at_munch1 W m m1 _ b Hb MU OFF RS) ltac:(lia) ltac:(cbn; lia)) as RD.
    rewrite Z.add_0_r in RD. exact RD.
  - destruct Hok as [Z0 | [R1 R2]]; [left; apply z8_of_unsigned0; exact Z0 | ].
    (* [comment removed for export] *)
    destruct (Z_lt_le_dec (X + s - 1) (X / 8 * 8 + 8)) as [SAME | NEXT].
    + destruct (ACC (X + s - 1 - a) ltac:(lia)) as (b' & Hb' & Hok'). replace (a + (X + s - 1 - a)) with (X + s - 1) in * by lia.
      assert (Es : shad (X + s - 1) = shad X) by (unfold shad; f_equal; clear - SAME Hs; Z.div_mod_to_equations; lia). rewrite Es in Hb'.
      assert (Eb : b' = b).
      { destruct Hb as (_ & _ & E1). destruct Hb' as (_ & _ & E2). specialize (E1 0%nat ltac:(cbn; lia)). specialize (E2 0%nat ltac:(cbn; lia)).
        cbn in E1, E2. rewrite Z.add_0_r in E1, E2. congruence. }
      subst b'. right. split; [exact R1|].
      destruct Hok' as [Z0 | [_ R4]]; [lia|]. clear - R2 R4 SAME Hs. Z.div_mod_to_equations. lia.
    + exfalso. destruct (ACC (X / 8 * 8 + 7 - a) ltac:(clear - H1 H2 NEXT Hs; Z.div_mod_to_equations; lia)) as (b7 & Hb7 & Hok7).
      replace (a + (X / 8 * 8 + 7 - a)) with (X / 8 * 8 + 7) in * by lia.
      assert (Es : shad (X / 8 * 8 + 7) = shad X) by (unfold shad; f_equal; clear; Z.div_mod_to_equations; lia). rewrite Es in Hb7.
      assert (Eb : b7 = b).
      { destruct Hb as (_ & _ & E1). destruct Hb7 as (_ & _ & E2). specialize (E1 0%nat ltac:(cbn; lia)). specialize (E2 0%nat ltac:(cbn; lia)).
        cbn in E1, E2. rewrite Z.add_0_r in E1, E2. congruence. }
      subst b7. destruct Hok7 as [Z0 | [R3 R4]]; [lia|]. clear - R3 R4. Z.div_mod_to_equations. lia.
Qed.
End WithSegs.

(* [comment removed for export] *)
Lemma ab_sxb_small : forall b : byte, 0 <= bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb. f_equal. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128. rewrite Z.mod_small by lia. lia.
Qed.
Lemma absh_cases : forall (b : byte) X s, absh_ok b X s ->
  b = z8 \/ (exists k, 0 < k < 8 /\ X mod 8 + s <= k /\ sxb b = Z_to_bv 64 k /\ zxb b = Z_to_bv 64 k).
Proof.
  intros b X s [H0 | [H1 H2]]; [left; exact H0 | right].
  exists (bv_unsigned b). split; [exact H1|]. split; [exact H2|]. split; [apply ab_sxb_small; lia | reflexivity].
Qed.
Lemma ab_land7 : forall X, 0 <= X -> Z.land X 7 = X mod 8.
Proof. intros X HX. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma ab_mod_mod8 : forall X, (X mod 18446744073709551616) mod 8 = X mod 8.
Proof.
  intros X. pose proof (Z.div_mod X 18446744073709551616 ltac:(lia)) as E.
  replace (X mod 8) with ((18446744073709551616 * (X / 18446744073709551616) + X mod 18446744073709551616) mod 8) by (rewrite <- E; reflexivity).
  replace (18446744073709551616 * (X / 18446744073709551616) + X mod 18446744073709551616)
     with (X mod 18446744073709551616 + (2305843009213693952 * (X / 18446744073709551616)) * 8) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma ab_land7w : forall X, Z.land (bv_unsigned (Z_to_bv 64 X)) 7 = X mod 8.
Proof.
  intros X. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  rewrite ab_land7 by (apply Z.mod_pos_bound; lia). apply ab_mod_mod8.
Qed.
Lemma ab_land7u : forall w : word, Z.land (bv_unsigned w) 7 = bv_unsigned w mod 8.
Proof. intros w. apply ab_land7. pose proof (bv_unsigned_in_range 64 w). lia. Qed.
Lemma ab_signed_small : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. rewrite zb_signed. rewrite unsigned_lit by lia.
  destruct (Z.ltb_spec0 x (2^63)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Class AsanImg (segs : list Segment) := { as_got_shb : Z ; as_reports : list Z }.

Section Classifier.
Context (segs : list Segment) {AI : AsanImg segs}.

Definition insn_at (pc : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 pc) with
  | Some w => match decode_any w with Some (i, _) => Some i | None => None end
  | None => None
  end.
Definition zr (r : reg) : Z := bv_unsigned r.
Definition i12 (i : bv 12) : Z := bv_signed i.
Definition i13 (i : bv 13) : Z := bv_signed i.
Definition i21 (i : bv 21) : Z := bv_signed i.
Definition auipc_tgt (pc : Z) (imm : bv 20) : Z := pc + Z.shiftl (bv_signed imm) 12.

(* [comment removed for export] *)
Definition call_to (pc : Z) (L : list Z) : bool :=
  match insn_at pc with
  | Some (Jal rd imm) => Z.eqb (zr rd) 1 && existsb (Z.eqb (pc + i21 imm)) L
  | Some (Auipc r imm) =>
      match insn_at (pc + 4) with
      | Some (Jalr rd rs lo) => Z.eqb (zr rd) 1 && Z.eqb (zr rs) (zr r) && existsb (Z.eqb (auipc_tgt pc imm + i12 lo)) L
      | _ => false
      end
  | _ => false
  end.
(* [comment removed for export] *)
Definition report_at (pc : Z) : bool :=
  call_to pc as_reports
  || match insn_at pc with
     | Some (OpImm ALU_ADD rd rs imm) => Z.eqb (zr rd) 10 && Z.eqb (i12 imm) 0 && call_to (pc + 4) as_reports
     | _ => false
     end.
(* [comment removed for export] *)
Definition slow_at (pc t : Z) : option (Z * Z * Z) :=
  match insn_at pc with
  | Some (OpImm ALU_AND u a i7) =>
      if Z.eqb (i12 i7) 7 && negb (Z.eqb (zr u) 0) then
        match insn_at (pc + 4) with
        | Some (OpImm ALU_ADD u1 u2 k) =>
            if Z.eqb (zr u1) (zr u) && Z.eqb (zr u2) (zr u) then
              match insn_at (pc + 8) with
              | Some (Branch c r1 r2 off) =>
                  if Z.eqb (zr r1) (zr u) && Z.eqb (zr r2) t then
                    match c with
                    | BC_LT => if report_at (pc + 12) then Some (zr u, i12 k + 1, pc + 8 + i13 off) else None
                    | BC_GE => if report_at (pc + 8 + i13 off) then Some (zr u, i12 k + 1, pc + 12) else None
                    | _ => None
                    end
                  else None
              | _ => None
              end
            else None
        | Some (Branch c r1 r2 off) =>
            if Z.eqb (zr r1) (zr u) && Z.eqb (zr r2) t then
              match c with
              | BC_LT => if report_at (pc + 8) then Some (zr u, 1, pc + 4 + i13 off) else None
              | BC_GE => if report_at (pc + 4 + i13 off) then Some (zr u, 1, pc + 8) else None
              | _ => None
              end
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Record achk := AChk { ck_t : Z ; ck_sg : bool ; ck_u : Z ; ck_sz : Z ; ck_jn : Z ; ck_eqf : bool }.

(* [comment removed for export] *)
Definition chk_at (pc : Z) : option achk :=
  match insn_at (pc - 4), insn_at pc with
  | Some (Load SZ1 sg t x i0), Some (Branch c t1 z off) =>
      if Z.eqb (zr t1) (zr t) && Z.eqb (zr z) 0 && Z.eqb (i12 i0) 0 && negb (Z.eqb (zr t) 0) then
        let T := pc + i13 off in let F := pc + 4 in
        match c with
        | BC_NE => if report_at T then Some (AChk (zr t) sg 0 8 F false)
                   else match slow_at T (zr t) with
                        | Some (u, s, J) => if Z.eqb J F then Some (AChk (zr t) sg u s F false) else None
                        | None => None
                        end
        | BC_EQ => if report_at F then Some (AChk (zr t) sg 0 8 T true)
                   else match slow_at F (zr t) with
                        | Some (u, s, J) => if Z.eqb J T then Some (AChk (zr t) sg u s T true) else None
                        | None => None
                        end
        | _ => None
        end
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition shload_at (pc : Z) : option (Z * achk) :=
  match insn_at pc, chk_at (pc + 4) with
  | Some (Load SZ1 _ t x _), Some c => Some (zr x, c)
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition addsh_at (pc : Z) : bool :=
  match insn_at pc, shload_at (pc + 4) with
  | Some (Op ALU_ADD d _ _), Some (x, _) => Z.eqb (zr d) x
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition srli_at (pc : Z) : option Z :=
  match insn_at pc with
  | Some (ShiftImm ALU_SRL t a sh) => if Z.eqb (bv_unsigned sh) 3 && addsh_at (pc + 4) then Some (zr a) else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition amat_at (pc : Z) : bool :=
  match insn_at pc, srli_at (pc + 4) with
  | Some (OpImm ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | Some (Op ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition shb1_at (pc : Z) : bool :=     (* [comment removed for export] *)
  match insn_at pc, insn_at (pc + 4) with
  | Some (Auipc y imm), Some (Load SZ8 _ y1 y2 lo) => Z.eqb (zr y1) (zr y) && Z.eqb (zr y2) (zr y) && Z.eqb (auipc_tgt pc imm + i12 lo) as_got_shb
  | _, _ => false
  end.
Definition farcall_at (pc : Z) : bool :=  (* [comment removed for export] *)
  match insn_at pc, insn_at (pc + 4) with
  | Some (Auipc y imm), Some (Jalr _ rs _) => Z.eqb (zr rs) (zr y)
  | _, _ => false
  end.

Inductive akind := AK0 | AKfeed | AKshload (c : achk) | AKchk (c : achk) | AKgot | AKshb.

Definition kind_at (pc : Z) : akind :=
  match chk_at pc with
  | Some c => AKchk c
  | None =>
  match shload_at pc with
  | Some (_, c) => AKshload c
  | None =>
      if addsh_at pc then AKfeed
      else match srli_at pc with
      | Some _ => AKfeed
      | None =>
      if amat_at pc then AKfeed
      else if shb1_at pc then AKfeed
      else if shb1_at (pc - 4) then AKgot
      else if shb1_at (pc - 8) then (match insn_at pc with Some (Load SZ8 _ _ _ lo) => if Z.eqb (i12 lo) 0 then AKshb else AK0 | _ => AK0 end)
      else if farcall_at pc then AKfeed
      else AK0
      end
  end end.
End Classifier.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ab_X ad :=
  match ad with
  | Z_to_bv 64 (?k + SHB)%Z => let _ := match tt with _ => is_Zlit k end in eval vm_compute in (k * 8)%Z     (* [comment removed for export] *)
  | Z_to_bv 64 (SHB + ?k)%Z => let _ := match tt with _ => is_Zlit k end in eval vm_compute in (k * 8)%Z
  | Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr (bv_unsigned (Z_to_bv 64 ?X)) 3)%Z => X
  | Z_to_bv 64 (Z.shiftr (bv_unsigned ?r) 3 + _)%Z => constr:(bv_unsigned r)
  | Z_to_bv 64 (_ + Z.shiftr (bv_unsigned ?r) 3)%Z => constr:(bv_unsigned r)
  | Z_to_bv 64 (Z.shiftr ?X 3 + _)%Z => X
  | Z_to_bv 64 (_ + Z.shiftr ?X 3)%Z => X
  | Z_to_bv 64 (?X / 8 + _)%Z => X
  | Z_to_bv 64 (_ + ?X / 8)%Z => X
  | Z_to_bv 64 (shad ?X) => X
  | wa (shad ?X) => X
  end.
(* [comment removed for export] *)
Ltac ab_alia := first [ lia | (unfold SHLO, SHHI in *; uchk_open; first [ lia | (Z.div_mod_to_equations; lia) ]) ].
(* [comment removed for export] *)
Ltac ab_addr :=
  unfold wa, shad; f_equal; rewrite ?unsigned_lit by ab_alia; rewrite ?Z.shiftr_div_pow2 by (clear; lia); change (2 ^ 3)%Z with 8%Z;
  unfold SHB; clear; Z.div_mod_to_equations; lia.
(* [comment removed for export] *)
Ltac ab_off := first [ assumption | (cbn [offshW]; unfold SHLO, SHHI; repeat (split; [lia|]); first [exact I | lia]) ].

(* [comment removed for export] *)
Ltac ashb := fail "ashb: no shadow-base cells for the current memory (override ApATac.ashb, or pose shb_cells/AH_shb facts)".

(* [comment removed for export] *)
Ltac ab_kind :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => eval vm_compute in (@kind_at segs _ pc)
  end.
Ltac show_kind := let k := ab_kind in idtac k.

(* [comment removed for export] *)
Ltac ab_shload s :=
  let ad := cur_mem_addr in
  let X := ab_X ad in
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mc _) =>
    first
      [ match goal with
        | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc |- _ =>
            let RD := fresh "RDsh" in
            pose proof (acc_rdG segs W mb mc a n X ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr)) as RD;
            Step.step; clear RD
        end
      | match goal with
        | ACC : acc segs ?mb ?a ?n, MU : munch ?W ?mb mc |- _ =>
            let RD := fresh "RDsh" in let b := fresh "shb_" in let OK := fresh "ABok" in
            destruct (acc_rdS segs W mb mc a n X s ad ACC MU ltac:(ab_off) ltac:(ab_alia) ltac:(ab_alia) ltac:(lia) ltac:(ab_alia) ltac:(ab_alia) ltac:(ab_addr))
              as (b & RD & OK);
            Step.step; clear RD
        end
      | fail 100 "ab: no (ACC : acc _ mb a n, MU : munch W mb <current mem>) pair of the context covers the" s "byte(s) accessed at" X ]
  end.

(* [comment removed for export] *)
Ltac ab_at_join := apply evt_done; eexists; eexists; map_cbv_set; reflexivity.
(* [comment removed for export] *)
Ltac ab_branch :=
  Step.step;
  first [ if_false | if_true
        | let KB := fresh "KBab" in
          if_cases KB; zify_cond KB; rewrite ?ab_land7w, ?ab_land7u in KB; rewrite ?ab_signed_small in KB by ab_alia;
          first [ exfalso; uchk_open; rewrite ?unsigned_lit in KB by lia; lia | clear KB ] ].

(* [comment removed for export] *)
Ltac ab_addi_opt :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let i := eval vm_compute in (insn_at segs pc) in
      lazymatch i with Some (OpImm ALU_ADD _ _ _) => Step.step | _ => idtac end
  end.

(* [comment removed for export] *)
Ltac ab_join t u J ABok :=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    let pt := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
    let pu := eval vm_compute in (bv_key (Z_to_bv 5 u)) in
    eapply (evt_cut segs (fun ms => exists vt vu : word, ms = MS (tset pu vu (tset pt vt R)) F (Z_to_bv 64 J) fc rv m ro));
    [ lazymatch type of ABok with
      | absh_ok ?b ?X ?s =>
          let k := fresh "k" in let K1 := fresh "K1" in let K2 := fresh "K2" in let Es := fresh "Es" in let Ez := fresh "Ez" in
          destruct (absh_cases b X s ABok) as [-> | (k & K1 & K2 & Es & Ez)];
          [ rewrite ?zxb_z8, ?sxb_z8; Step.step; try first [if_false | if_true]; ab_at_join
          | rewrite ?Es, ?Ez; clear Es Ez;
            ab_branch;                                   (* [comment removed for export] *)
            Step.step; ab_addi_opt;                      (* [comment removed for export] *)
            rewrite ?ab_land7w, ?ab_land7u;
            ab_branch;                                   (* [comment removed for export] *)
            ab_at_join ]
      end
    | let ms1 := fresh "ms" in let vt := fresh "abt" in let vu := fresh "abu" in
      intros ms1 (vt & vu & ->); map_cbv_set; clear ABok ]
  end.

(* [comment removed for export] *)
Ltac ab_chk t u s J :=
  first
    [ (* [comment removed for export] *)
      lazymatch goal with
      | ABok : absh_ok ?b _ _ |- _ => fail
      | |- _ => Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true]
      end
    | (* [comment removed for export] *)
      lazymatch goal with
      | ABok : absh_ok ?b ?X ?sz |- _ =>
          let E := fresh "Eab" in
          assert (E : b = z8)
            by (destruct ABok as [E | [K1 K2]]; [exact E | exfalso; (uchk_open; Z.div_mod_to_equations; lia)]);
          subst b; clear ABok; Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true]
      end
    | lazymatch goal with
      | ABok : absh_ok ?b ?X ?sz |- _ =>
          lazymatch u with
          | 0%Z => fail 100 "ab: the shadow byte at" X "may be non-zero but the check has no slow path (whole-granule access of" s "bytes): the acc range must cover the granule"
          | _ => ab_join t u J ABok
          end
      end
    | fail 100 "ab: cannot decide the check branch (t =" t ", join" J ")" ].

(* [comment removed for export] *)
Ltac ab1 :=
  let k := ab_kind in
  lazymatch k with
  | AK0 => fail
  | AKfeed => Step.step
  | AKshload (AChk _ _ _ ?s _ _) => ab_shload s
  | AKchk (AChk ?t _ ?u ?s ?J _) => ab_chk t u s J
  | AKgot => first [ Step.step | ashb; Step.step ]
  | AKshb => first [ Step.step | ashb; Step.step ]
  end.
Ltac ab := repeat ab1.

(* [comment removed for export] *)
Ltac apre := ual; ab; repeat (progress ub; ab).

(* [comment removed for export] *)
Ltac show_pcA := lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "pc =" pc | |- _ => idtac "(no machine state)" end.
