(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp OpsTwin GSeal.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G4A.

Definition wm8 : w64 := wsub wzero (wlit 8%uint63).
Definition two40 : w64 := wlit 1099511627776%uint63.

Definition kinds_lit (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with Some _ => true | None => false end) ws.

Definition no_kind5 (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with Some k => negb (k =? 5) | None => false end) ws.

Fixpoint exists_lazy {A} (f : A -> bool) (l : list A) : bool :=
  match l with [] => false | a :: t => if f a then true else exists_lazy f t end.
Lemma exists_lazy_eq : forall A (f : A -> bool) l, exists_lazy f l = existsb f l.
Proof. induction l as [|a t IH]; cbn [exists_lazy existsb]; [reflexivity|]. rewrite IH. destruct (f a); reflexivity. Qed.
Definition fits_decided (fs : list fact) (zfree : sv) (cands : list sv) : bool :=
  exists_lazy (fun c => match decide_ltu fs zfree c with Some false => true | _ => false end) cands.

Definition anchor_facts (fs : list fact) (k : int) (dlo dhi : Z) (kA : int) : list fact :=
  match find_range fs k with
  | Some (lo, hi) =>
      if negb (wt lo) && negb (wt hi) && (0 <=? dlo) && (dlo <=? dhi) && (w2Z hi + dhi <? two63)
      then [FRange kA (wlit (Uint63.of_Z (w2Z lo + dlo))) (wlit (Uint63.of_Z (w2Z hi + dhi)))] else []
  | None => []
  end.

Definition range_known (fs : list fact) (k : int) : bool :=
  match find_range fs k with Some (lo, hi) => negb (wt hi) | None => false end.

Definition range_nz (fs : list fact) (k : int) : bool :=
  match find_range fs k with Some (lo, hi) => negb (wt hi) && negb (weqb lo wzero) | None => false end.

Definition win_region_ok (st : sstate) (own : list int) (w : sv * sv * sv) : bool :=
  match w with
  | (lo, len, VL kd) =>
      negb (wt kd) && ((PrimInt63.eqb (wl kd) 0%uint63)
                       || ((PrimInt63.leb 7%uint63 (wl kd))
                       || match lo with
                          | VP k o =>
                              weqb o wzero && negb (PrimInt63.eqb k 0%uint63)
                              && match IMap.find k (s_regs st) with
                                 | Some r => PrimInt63.eqb (rg_lo r) 0%uint63
                                             && (if PrimInt63.eqb (wl kd) 1%uint63
                                                 then match decide_ltu (s_facts st) (VL wzero) (rg_hi r) with Some true => true | _ => false end
                                                 else sv_eqb (rg_hi r) len)
                                 | None => false
                                 end
                          | _ => false
                          end))
  | _ => false
  end.

Definition no_other_at (kC : int) (w0 : sv * sv * sv) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match w with (VP k _, _, _) => negb (PrimInt63.eqb k kC) || win3_eqb w w0 | _ => true end) ws.

Definition zone_facts (kA : int) (SZ zptr zfree : sv) : list fact :=
  [FULe zptr (VP kA wzero); FULe (VAlu ALU_ADD (VP kA wzero) SZ) (VAlu ALU_ADD zptr zfree)].

Definition two40Z : Z := 1099511627776.
Definition sz_small (fs : list fact) (SZ : sv) : bool :=
  match decide_ltu fs SZ (VL two40) with
  | Some true => true
  | _ =>
      match SZ with
      | VAlu ALU_SUB (VAlu ALU_SLL x (VL a)) (VAlu ALU_SLL x' (VL b)) =>
          sv_eqb x x' && PrimInt63.leb (shamt6 b) (shamt6 a) && negb (wt (snd (sv_bounds fs x)))
          && Z.ltb (w2Z (snd (sv_bounds fs x)) * 2 ^ (to_Z (shamt6 a))) two40Z
      | _ => false
      end
  end.

Lemma sz_small_sound : forall E fs SZ, facts_hold E fs -> sz_small fs SZ = true -> bv_unsigned (den E SZ) < two40Z.
Proof.
  intros E fs SZ FH H. unfold sz_small in H.
  destruct (decide_ltu fs SZ (VL two40)) as [[|]|] eqn:DB.
  { pose proof (decide_ltu_sound E fs FH _ _ _ DB) as SZB. apply (proj1 (ltu_iff _ _ true)) in SZB.
    cbn [den] in SZB. rewrite wbv_unsigned in SZB. change (w2Z two40) with two40Z in SZB. exact SZB. }
  all: destruct SZ as [| |op a b| | | | | | | |]; try discriminate; destruct op; try discriminate;
       destruct a as [| |opa x sa| | | | | | | |]; try discriminate; destruct opa; try discriminate;
       destruct sa as [ca| | | | | | | | | |]; try discriminate;
       destruct b as [| |opb x' sb| | | | | | | |]; try discriminate; destruct opb; try discriminate;
       destruct sb as [cb| | | | | | | | | |]; try discriminate.
  all: apply andb_prop in H as [H LT]; apply andb_prop in H as [H NT]; apply andb_prop in H as [XX LE];
       apply sv_eqb_eq in XX; subst x'; apply Z.ltb_lt in LT; apply negb_true_iff in NT;
       apply Uint63.leb_spec in LE.
  all: pose proof (sv_bounds_sound E fs FH x) as BX; destruct (sv_bounds fs x) as [l h] eqn:B; unfold inb in BX; cbn [fst snd] in BX, LT, NT.
  all: pose proof (shamt6_range ca) as RA; pose proof (shamt6_range cb) as RB.
  all: pose proof (bv_unsigned_in_range _ (den E x)) as RX; rewrite bv_modulus_64 in RX.
  all: assert (PA : 0 < 2 ^ to_Z (shamt6 ca)) by (apply Z.pow_pos_nonneg; lia);
       assert (PB : 0 < 2 ^ to_Z (shamt6 cb)) by (apply Z.pow_pos_nonneg; lia);
       assert (PLE : 2 ^ to_Z (shamt6 cb) <= 2 ^ to_Z (shamt6 ca)) by (apply Z.pow_le_mono_r; lia).
  all: cbn [den alu64 alu]; rewrite bv_sub_unsigned, !bv_shiftl_unsigned, !shamt6_bv, !Z.shiftl_mul_pow2 by apply int_range.
  all: unfold bv_wrap; rewrite bv_modulus_64; pose proof (w2Z_range h) as RH; unfold two40Z in *.
  all: assert (M1 : bv_unsigned (den E x) * 2 ^ to_Z (shamt6 ca) < 1099511627776) by nia.
  all: assert (M2 : 0 <= bv_unsigned (den E x) * 2 ^ to_Z (shamt6 cb) <= bv_unsigned (den E x) * 2 ^ to_Z (shamt6 ca)) by nia.
  all: rewrite (Z.mod_small (bv_unsigned (den E x) * 2 ^ to_Z (shamt6 cb)) two64) by (unfold two64; nia).
  all: rewrite (Z.mod_small (bv_unsigned (den E x) * 2 ^ to_Z (shamt6 ca)) two64) by (unfold two64; nia).
  all: rewrite Z.mod_small by (unfold two64; nia).
  all: nia.
Qed.

Section WithPc.
Variable CARVE_PC : int.
Variables rR rSZ : r5.

Definition new_region (SZ : sv) : region := Region 0%uint63 SZ true BGNone IMap.empty.

Definition g4a_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let fs := s_facts st in let n := s_next st in
          let R := getr st rR in let SZ := getr st rSZ in
          if negb (r5_eqb rR X0) && st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i
             && Z.ltb (Z.of_nat (length ws)) 4096 && kinds_lit ws && no_kind5 ws
             && sz_small fs SZ
          then
            match zptr with
            | VP kZP ozp =>
                if weqb ozp wzero && negb (PrimInt63.eqb kZP 0%uint63) then

                if (if sv_eqb R zptr then fits_decided fs zfree [SZ; sv_alu ALU_SUB R (sv_alu ALU_SUB zptr SZ);
                                                         sv_alu ALU_ADD (sv_alu ALU_SUB R zptr) SZ;
                                                         sv_alu ALU_ADD SZ (sv_alu ALU_SUB R zptr)] else false) then
                  Some [setr (surg st [] [(n, new_region SZ)] (mk_args 1%uint63 aw (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))]) ca)
                                  ([FEq (VP n wzero) R] ++ zone_facts n SZ zptr zfree ++ anchor_facts fs kZP 0 0 n
                                   ++ (if PrimInt63.leb 3%uint63 (find_align fs kZP) then [FAlign n 3%uint63] else []))
                                  (PrimInt63.add n 1%uint63)) rR (VP n wzero)]

                else if (if sv_eqb R (sv_alu ALU_AND (sv_alu ALU_ADD zptr (VL (wlit 7%uint63))) (VL wm8)) && range_known fs kZP
                         then fits_decided fs zfree [sv_alu ALU_SUB R (sv_alu ALU_SUB zptr SZ);
                                                  sv_alu ALU_ADD (sv_alu ALU_SUB R zptr) SZ;
                                                  sv_alu ALU_ADD SZ (sv_alu ALU_SUB R zptr)] else false) then
                  Some [setr (surg st [] [(n, new_region SZ)] (mk_args 1%uint63 aw (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))]) ca)
                                  ([FEq (VP n wzero) R; FAlign n 3%uint63] ++ zone_facts n SZ zptr zfree ++ anchor_facts fs kZP 0 7 n)
                                  (PrimInt63.add n 1%uint63)) rR (VP n wzero)]

                else match R with
                | VP kC oc =>
                    if weqb oc (wlit 8%uint63) && negb (PrimInt63.eqb kC 0%uint63) && negb (PrimInt63.eqb kC kZP)
                       && PrimInt63.leb 4%uint63 (find_align fs kC) && range_nz fs kC
                       && forallb (win_region_ok st [kC]) ws then
                    match IMap.find kC (s_regs st) with
                    | Some rc =>
                        match rg_hi rc, cell_at rc 0 8%uint63 with
                        | VL hlen, Some hd =>
                            let sz := wsub hlen (wlit 8%uint63) in
                            if negb (wt hlen) && PrimInt63.eqb (rg_lo rc) 0%uint63 && rg_w rc
                               && existsb (win3_eqb (VP kC wzero, VL hlen, VL (wlit 1%uint63))) ws
                               && no_other_at kC (VP kC wzero, VL hlen, VL (wlit 1%uint63)) ws
                               && sv_eqb hd c0 && wleu (wlit 8192%uint63) sz && negb (wt sz)
                               && match decide_ltu fs (VL sz) SZ with Some false => true | _ => false end

                               && PrimInt63.eqb (PrimInt63.land (wl sz) 7%uint63) 0%uint63
                               && GSeal.twins_explained st kC [cb; vb] ws
                            then
                              let ws' := List.filter (fun w => negb (win3_eqb w (VP kC wzero, VL hlen, VL (wlit 1%uint63)))) ws
                                         ++ [(VP n wzero, SZ, VL (wlit 5%uint63))] in
                              let ca' := [root; cb; ce; ccap; vb; ve; vcap; VP n wzero; VL sz; VP kC wzero; slot; tD; restD; rootT; n1; P1; zh] in
                              Some [setr (surg st [kC] [(n, new_region SZ)] (mk_args 1%uint63 aw ws' ca')
                                              ([FEq (VP n wzero) R; FAlign n 3%uint63] ++ zone_facts n SZ (VP n wzero) (VL sz) ++ anchor_facts fs kC 8 8 n)
                                              (PrimInt63.add n 1%uint63)) rR (VP n wzero)]
                            else None
                        | _, _ => None
                        end
                    | None => None
                    end
                    else None
                | _ => None
                end
                else None
            | _ => None
            end
          else None
      | _ => None
      end
      else None
  | None => None
  end.

Definition g4a_contract : contract := Contract CARVE_PC g4a_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma kinds_lit_kind : forall E ws, kinds_lit ws = true -> forall x, In x ws -> exists kd, kind_of x = Some kd /\ w_kind (wden E x) = kd.
Proof.
  intros E ws H x Hx. pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [kd|] eqn:K; [|discriminate]. exists kd. split; [reflexivity| exact (kind_of_sound E x kd K)].
Qed.

Lemma no_kind5_sound : forall E ws, no_kind5 ws = true -> forall w, In w (map (wden E) ws) -> w_kind w <> K_ZONE.
Proof.
  intros E ws H w Hw. apply in_map_iff in Hw as (x & <- & Hx).
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [kd|] eqn:KD; [|discriminate]. rewrite (kind_of_sound E x kd KD).
  destruct (Z.eqb_spec kd 5); [discriminate|]. unfold K_ZONE. exact n.
Qed.

Lemma anchor_facts_sound : forall E fs k dlo dhi kA, facts_hold E fs ->
  bv_unsigned (ev E k) + dlo <= bv_unsigned (ev E kA) <= bv_unsigned (ev E k) + dhi ->
  Forall (fact_holds E) (anchor_facts fs k dlo dhi kA).
Proof.
  intros E fs k dlo dhi kA FH B. unfold anchor_facts.
  destruct (find_range fs k) as [[lo hi]|] eqn:FR; [|constructor].
  destruct (negb (wt lo) && negb (wt hi) && (0 <=? dlo) && (dlo <=? dhi) && (w2Z hi + dhi <? two63)) eqn:C; [|constructor].
  apply andb_prop in C as [C H5]. apply andb_prop in C as [C H4]. apply andb_prop in C as [C H3]. apply andb_prop in C as [H1 H2].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
  pose proof (find_range_sound_gen E fs FH k lo hi FR) as [R1 R2]. pose proof (w2Z_range lo). pose proof (w2Z_range hi).
  constructor; [|constructor]. cbn [fact_holds]. rewrite !wlit_ok, !of_Z_small by (unfold two63 in *; lia). lia.
Qed.

Lemma zone_facts_sound : forall E kA SZ zptr zfree r0 rest,
  bv_unsigned (ev E kA) = r0 -> bv_unsigned (den E zptr) <= r0 ->
  r0 + bv_unsigned (den E SZ) <= bv_unsigned (den E zptr) + bv_unsigned (den E zfree) ->
  bv_unsigned (den E zptr) + bv_unsigned (den E zfree) < two64 ->
  Forall (fact_holds E) rest ->
  Forall (fact_holds E) (zone_facts kA SZ zptr zfree ++ rest).
Proof.
  intros E kA SZ zptr zfree r0 rest EQ H1 H2 H3 REST. pose proof (bv_unsigned_in_range _ (den E SZ)) as RS. rewrite bv_modulus_64 in RS.
  pose proof (bv_unsigned_in_range _ (den E zptr)) as RP. rewrite bv_modulus_64 in RP.
  unfold zone_facts. cbn [app]. constructor; [| constructor; [| exact REST]].
  - cbn [fact_holds]. rewrite (den_VP0 E kA wzero (weqb_refl _)), EQ. exact H1.
  - change (bv_unsigned (alu64 ALU_ADD (den E (VP kA wzero)) (den E SZ)) <= bv_unsigned (alu64 ALU_ADD (den E zptr) (den E zfree))).
    cbn [alu64 alu]. rewrite !bv_add_unsigned, (den_VP0 E kA wzero (weqb_refl _)), EQ. unfold bv_wrap. rewrite !bv_modulus_64.
    rewrite !Z.mod_small by (unfold two64 in *; lia). exact H2.
Qed.

Lemma safe_fresh : forall md g LB ws a,
  pure_ok g -> own_ok g LB -> (forall w, In w ws -> w_kind w <> K_ZONE) ->
  z_ptr (u_zone g) <= a < z_ptr (u_zone g) + z_free (u_zone g) -> safe md g ws a.
Proof.
  intros md g LB ws a P O N5 Ha w Hw SO Hin. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV & LV & LA & ZV).
  destruct (head_chunk g P) as (h & r & EH & H1 & H2 & H3).
  assert (Hh : In h (z_chunks (u_zone g))) by (rewrite EH; left; reflexivity).
  unfold sub_ok in SO. cbv zeta in SO.
  destruct SO as [(KD & I1 & I2 & I3)|[(KD & I1 & I2 & I3)|[(KD & lD & HlD & I2 & I3)|(KD & I2 & I3)]]].
  - pose proof (disj_cc g LB O h Hh) as D. unfold chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
  - pose proof (disj_vc g LB O h Hh) as D. unfold chunk_lo, chunk_hi, v_end, v_capend, v_bytes, rdisj, CHUNK_HDR in *. nia.
  - destruct (top_level g lD HlD) as (ls0 & EL & _ & HinD). destruct (level_array g P lD HinD) as (V & A & G1 & G2 & G4' & c & Hc & IC).
    pose proof (in_alloc_fresh_disj (u_zone g) (lv_P lD) (lv_bytes lD) a 1 ZV ltac:(pose proof (level_geom lD V); unfold OBJ_SIZE in *; lia) A
                  ltac:(lia) ltac:(rewrite EH; cbn [hd]; lia)) as D.
    assert (lv_slot lD <= w_lo w) by (destruct (md =? CM_CONS); unfold OBJ_SIZE in *; lia). unfold rdisj in D. lia.
  - exact (N5 w Hw KD).
Qed.

Lemma wrap64 : forall x, bv_wrap 64 x = x mod two64.
Proof. intros x. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. Qed.

Lemma cand_vals : forall E R zptr SZ,
  let r := bv_unsigned (den E R) in let zp := bv_unsigned (den E zptr) in let sz := bv_unsigned (den E SZ) in
  bv_unsigned (den E (sv_alu ALU_SUB R (sv_alu ALU_SUB zptr SZ))) = (r - zp + sz) mod two64 /\
  bv_unsigned (den E (sv_alu ALU_ADD (sv_alu ALU_SUB R zptr) SZ)) = (r - zp + sz) mod two64 /\
  bv_unsigned (den E (sv_alu ALU_ADD SZ (sv_alu ALU_SUB R zptr))) = (r - zp + sz) mod two64.
Proof.
  intros E R zptr SZ. cbv zeta. rewrite !den_sv_alu. cbn [alu64 alu].
  rewrite ?bv_sub_unsigned, ?bv_add_unsigned, ?bv_sub_unsigned, !wrap64. unfold two64.
  split; [| split].
  - rewrite Zminus_mod_idemp_r. f_equal; lia.
  - rewrite Zplus_mod_idemp_l. f_equal; lia.
  - rewrite Zplus_mod_idemp_r. f_equal; lia.
Qed.

Lemma g4a_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> g4a_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP.
  unfold g4a_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND BND]. apply andb_prop in COND as [COND NK5]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND WLEN]. apply Z.ltb_lt in WLEN.
  apply andb_prop in COND as [COND N62]. apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [RX0 VB].
  apply negb_true_iff in RX0. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in N62.
  assert (RNX : rR <> X0) by (intros X; rewrite X in RX0; discriminate).
  destruct zptr as [|kZP ozp| | | | | | | | |]; try discriminate.
  destruct (weqb ozp wzero && negb (PrimInt63.eqb kZP 0)) eqn:CZ; [|discriminate].
  apply andb_prop in CZ as [OZ KZ0]. apply (proj1 (weqb_ok _ _)) in OZ. subst ozp. apply negb_true_iff in KZ0.
  set (n := s_next st) in *. set (R := getr st rR) in *. set (SZ := getr st rSZ) in *.
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).

  pose proof HS0 as [Ppc0 Px00 Pregs0 _ _ _ _ _ _ Pbst0 _ _ _ _ _ _ _ _].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (INCA : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; VP kZP wzero; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INAW : In aw (op_args o)) by (rewrite ARGS; right; left; reflexivity).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (KZPn : PrimInt63.ltb kZP n = true) by exact (VBo (VP kZP wzero) (INCA (VP kZP wzero) ltac:(do 7 right; left; reflexivity))).
  apply Uint63.ltb_spec in KZPn.
  assert (VBrf : rf_allb (sv_vars_below n) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBR : sv_vars_below n R = true) by (subst R; unfold getr; exact (rf_allb_get _ _ _ VBrf rR)).
  assert (VBSZ : sv_vars_below n SZ = true) by (subst SZ; unfold getr; exact (rf_allb_get _ _ _ VBrf rSZ)).

  set (E' := env_upd E n (den E R)).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  assert (EVn : ev E' n = den E R) by apply env_upd_same.
  assert (DRR : den E' R = den E R) by exact (den_reval n E E' HX R VBR).
  assert (DRSZ : den E' SZ = den E SZ) by exact (den_reval n E E' HX SZ VBSZ).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n E E' HX v (VBo v Hv))).
  assert (EVkZP : ev E' kZP = ev E kZP) by exact (ev_reval n E E' HX kZP ltac:(apply Uint63.ltb_spec; exact KZPn)).
  clearbody E'.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear HS0 Ppc0 Px00 Pregs0 Pbst0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E') as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV' & LV & LA & ZV).
  pose proof ZV as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  destruct (head_chunk g P) as (h & hr & EH & HH1 & HH2 & HH3).
  assert (Hh : In h (z_chunks (u_zone g))) by (rewrite EH; left; reflexivity).
  pose proof (owned_chunk g h Hh) as OWNh.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block h) HA (proj1 O _ OWNh)) as (Bh1 & Bh2 & Bh3 & Bh4 & _).
  unfold chunk_block in Bh1, Bh2, Bh3. cbn [fst snd] in Bh1, Bh2, Bh3.
  assert (ZPV : bv_unsigned (ev E' kZP) = z_ptr (u_zone g)) by (rewrite Lzp; symmetry; exact (den_VP0 E' kZP wzero (weqb_refl _))).
  pose proof (N5 := no_kind5_sound E' ws NK5).

  pose proof (sz_small_sound E' (s_facts st) SZ Pfacts BND) as SZB. unfold two40Z in SZB.
  set (sz := bv_unsigned (den E' SZ)) in *. set (zp := z_ptr (u_zone g)) in *. set (zf := z_free (u_zone g)) in *.
  pose proof (bv_unsigned_in_range _ (den E' SZ)) as RSZ. rewrite bv_modulus_64 in RSZ. fold sz in RSZ.

  assert (BYF : forall a, zp <= a < zp + zf ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E') ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (owned_byte_props segs IMGX AW _ LB (ms_mem ms) model 1 g (map (wden E') ws) (chunk_block h) a HA WF O Wk OWNh).
    - unfold in_iv, chunk_block, chunk_lo, chunk_hi, CHUNK_HDR in *. cbn [fst snd]. lia.
    - exact (safe_fresh 1 g LB (map (wden E') ws) a P O N5 Ha). }
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E') ws) a -> FP OPS E' (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E') ws) _ a DEC)). auto. }
  assert (Lzf' : bv_unsigned (den E' zfree) = zf) by (symmetry; exact Lzf).
  assert (HIZN : hiZ E' (new_region SZ) = sz) by reflexivity.
  assert (LOZN : loZ (new_region SZ) = 0) by reflexivity.
  assert (CHI : chunk_hi h = zp + zf) by (subst zp zf; lia).
  assert (ZP0 : 8 <= zp) by (pose proof HH1 as X; unfold chunk_lo, CHUNK_HDR in X; subst zp; lia).

  assert (REGOK : forall r0, zp <= r0 -> r0 + sz <= zp + zf -> bv_unsigned (ev E' n) = r0 ->
            region_ok segs (s_priv st) E' (ms_mem ms) n (new_region SZ)).
  { intros r0 H1 H2 EQ. apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n (new_region SZ) NZ).
    - exact I.
    - reflexivity.
    - rewrite LOZN, EQ. unfold chunk_lo, chunk_hi, CHUNK_HDR in *. lia.
    - rewrite HIZN, EQ. unfold chunk_lo, chunk_hi, CHUNK_HDR in *. lia.
    - intros a Ha. rewrite LOZN, HIZN, EQ in Ha. destruct (BYF a ltac:(lia)) as (_ & _ & _ & MT & NS). auto.
    - intros gk gr F. cbn [new_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }
  assert (NRFP : forall r0, zp <= r0 -> r0 + sz <= zp + zf -> bv_unsigned (ev E' n) = r0 ->
            forall a, inR E' n (new_region SZ) a -> FP OPS E' (op_args o) a).
  { intros r0 H1 H2 EQ a IR. unfold inR in IR. rewrite LOZN, HIZN, EQ in IR.
    destruct (BYF a ltac:(lia)) as (RA & NI & NW & _). exact (FPold a ltac:(lia) NI NW). }
  assert (WINWF : forall r0, zp <= r0 -> r0 + sz <= zp + zf -> bv_unsigned (ev E' n) = r0 ->
            window_wf LB (aw_ceiling segs IMGX AW model) (wden E' (VP n wzero, SZ, VL (wlit 5%uint63)))).
  { intros r0 H1 H2 EQ. unfold wden. rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ. fold sz. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 5%uint63) with 5.
    unfold window_wf. cbn [w_lo w_len w_kind w_iv]. unfold chunk_lo, chunk_hi, CHUNK_HDR in *.
    split; [lia|]. split; [lia|]. split; [lia|]. right; right. split; [unfold K_SUB; lia|].
    exists (chunk_block h). split; [exact (proj1 O _ OWNh)|]. intros a Ha. unfold in_iv, chunk_block, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold CHUNK_HDR. lia. }
  assert (SUBOK : forall r0, zp <= r0 -> r0 + sz <= zp + zf -> bv_unsigned (ev E' n) = r0 ->
            sub_ok 1 g (wden E' (VP n wzero, SZ, VL (wlit 5%uint63)))).
  { intros r0 H1 H2 EQ. unfold wden. rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ. fold sz. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 5%uint63) with 5.
    unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; right; right. split; [reflexivity|]. rewrite EH. cbn [hd]. fold zp. lia. }

  assert (FITS : forall r0 nf, zp <= r0 -> r0 + sz <= zp + zf -> bv_unsigned (ev E' n) = r0 -> Forall (fact_holds E') nf ->
            st_ok segs OPS E' (setr (surg st [] [(n, new_region SZ)] (mk_args 1%uint63 aw (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))])
                                                 [root; cb; ce; ccap; vb; ve; vcap; VP kZP wzero; zfree; c0; slot; tD; restD; rootT; n1; P1; zh])
                                          nf (PrimInt63.add n 1)) rR (VP n wzero)) ms model).
  { intros r0 nf H1 H2 EQ NF.
    assert (LEN' : Z.of_nat (length (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))])) < two63) by (rewrite length_app; cbn [length]; unfold two63; lia).
    apply setreg_sound; [| exact RNX| transitivity (den E' R); [reflexivity|]; rewrite DRR, <- EVn; apply bv_eq; rewrite (den_VP0 E' n wzero (weqb_refl _)); reflexivity].
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [(n, new_region SZ)] _ _ (PrimInt63.add n 1)).
    - intros k [].
    - constructor; [intros []| constructor].
    - intros k r [H|[]]. injection H as <- <-. exact NZ.
    - intros k r [H|[]]. injection H as <- <-. exact (REGOK r0 H1 H2 EQ).
    - intros k r a [H|[]] IR. injection H as <- <-. left. exact (NRFP r0 H1 H2 EQ a IR).
    - intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE12. injection X1 as <- <-. injection X2 as <- <-. contradiction.
    - rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 1, (den E' aw), (map (wden E') (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))])),
             (map (den E') [root; cb; ce; ccap; vb; ve; vcap; VP kZP wzero; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]), LB.
      split; [apply mk_args_sound; exact LEN'|]. split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite map_app; apply wins_keep_app; intros w0 [<-|[]]; apply UOK.kind_sub_untied; vm_compute; reflexivity|]. split.
      + unfold windows_wf in *. rewrite map_app. apply Forall_app. split; [exact WF|]. constructor; [exact (WINWF r0 H1 H2 EQ)| constructor].
      + cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
        assert (NP : forall w, In w (map (wden E') (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))])) -> pot_win w -> In w (map (wden E') ws)).
        { apply UOK.pot_map_old. intros x Hx. apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact Hx| right; apply kind_ne; vm_compute; reflexivity]. }
        exists g. split; [exact L| split; [exact P| split; [exact O| split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ (proj1 CS0) NP)| split; [exact (acct_pot_ws _ _ _ _ _ (proj1 (proj2 CS0)) NP)|]]]]]]].
        { unfold wins_ok in *. rewrite map_app. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
          intros _. right. split; [| exact (SUBOK r0 H1 H2 EQ)].
          unfold wden. cbn [den w_kind]. rewrite wbv_unsigned, wlit_ok. change (to_Z 5%uint63) with 5. unfold K_BLOCK. lia. }

        rewrite map_app. apply SealX.seal_ok_app_other; [exact (proj2 (proj2 CS0))|]. intros w [<-|[]]. apply kind_ne. vm_compute. reflexivity.
    - intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') (ws ++ [(VP n wzero, SZ, VL (wlit 5%uint63))])) _ a (mk_args_sound E' 1%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
      rewrite map_app in NW. split.
      + left. apply (FPold a RA NI). intros X. apply NW. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
      + intros k r [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
        cbn [map]. unfold wden at 1. rewrite (den_VP0 E' n wzero (weqb_refl _)). unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite LOZN, HIZN in IR. fold sz. lia.
    - exact NF. }

  destruct (if sv_eqb R (VP kZP wzero) then fits_decided (s_facts st) zfree [SZ; sv_alu ALU_SUB R (sv_alu ALU_SUB (VP kZP wzero) SZ);
                                            sv_alu ALU_ADD (sv_alu ALU_SUB R (VP kZP wzero)) SZ; sv_alu ALU_ADD SZ (sv_alu ALU_SUB R (VP kZP wzero))] else false) eqn:C1.
  {
    change (sv_eqb R (VP kZP wzero) && fits_decided (s_facts st) zfree [SZ; sv_alu ALU_SUB R (sv_alu ALU_SUB (VP kZP wzero) SZ);
                                            sv_alu ALU_ADD (sv_alu ALU_SUB R (VP kZP wzero)) SZ; sv_alu ALU_ADD SZ (sv_alu ALU_SUB R (VP kZP wzero))] = true) in C1.
    apply andb_prop in C1 as [RQ FD]. apply sv_eqb_eq in RQ.
    assert (RV : bv_unsigned (den E' R) = zp) by (rewrite RQ, (den_VP0 E' kZP wzero (weqb_refl _)); exact ZPV).
    assert (LE : sz <= zf).
    { unfold fits_decided in FD. rewrite exists_lazy_eq in FD. pose proof (cand_vals E' R (VP kZP wzero) SZ) as (V1 & V2 & V3). cbv zeta in V1, V2, V3.
      rewrite RV, (den_VP0 E' kZP wzero (weqb_refl _)), ZPV in V1, V2, V3. fold sz in V1, V2, V3.
      replace (zp - zp + sz) with sz in V1, V2, V3 by lia.
      assert (SMALL : sz mod two64 = sz) by (apply Z.mod_small; unfold two64; lia).
      rewrite SMALL in V1, V2, V3.
      cbn [existsb] in FD. rewrite orb_false_r in FD.
      repeat (apply orb_prop in FD as [FD|FD]);
        match type of FD with (match decide_ltu ?fs ?a ?b with _ => _ end) = true =>
          destruct (decide_ltu fs a b) as [[|]|] eqn:DF; try discriminate;
          pose proof (decide_ltu_sound E' (s_facts st) Pfacts _ _ _ DF) as LE; apply (proj1 (ltu_iff _ _ false)) in LE;
          rewrite Lzf' in LE; first [rewrite V1 in LE | rewrite V2 in LE | rewrite V3 in LE | fold sz in LE]; lia
        end. }
    assert (EQ : bv_unsigned (ev E' n) = zp) by (rewrite EVn, <- DRR; exact RV).
    injection AP as <-. apply (FITS zp); [lia| lia| exact EQ|].
    constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, <- DRR. reflexivity. }
    apply (zone_facts_sound E' n SZ (VP kZP wzero) zfree zp _ EQ); rewrite ?(den_VP0 E' kZP wzero (weqb_refl _)), ?ZPV, ?Lzf'; fold sz; [lia| lia| unfold chunk_lo, chunk_hi, CHUNK_HDR in *; lia|].
    apply Forall_app. split.
    { apply anchor_facts_sound; [exact Pfacts|]. rewrite ZPV, EQ. fold zp. lia. }
    destruct (PrimInt63.leb 3 (find_align (s_facts st) kZP)) eqn:AL; [|constructor]. constructor; [|constructor].
    cbn [fact_holds]. rewrite EQ. change (2 ^ to_Z 3%uint63) with 8. fold zp in ZPV. rewrite <- ZPV.
    pose proof (find_align_sound_gen E' (s_facts st) Pfacts kZP) as A. apply Uint63.leb_spec in AL. change (to_Z 3%uint63) with 3 in AL.
    pose proof (int_range (find_align (s_facts st) kZP)).
    replace (2 ^ to_Z (find_align (s_facts st) kZP)) with (8 * 2 ^ (to_Z (find_align (s_facts st) kZP) - 3)) in A
      by (replace (to_Z (find_align (s_facts st) kZP)) with (3 + (to_Z (find_align (s_facts st) kZP) - 3)) at 2 by lia; rewrite Z.pow_add_r by lia; reflexivity).
    assert (PP : 0 < 2 ^ (to_Z (find_align (s_facts st) kZP) - 3)) by (apply Z.pow_pos_nonneg; lia).
    apply Z.mod_divide in A; [|lia]. apply Z.mod_divide; [lia|]. destruct A as [q Hq]. exists (q * 2 ^ (to_Z (find_align (s_facts st) kZP) - 3)). lia. }
  destruct (if sv_eqb R (sv_alu ALU_AND (sv_alu ALU_ADD (VP kZP wzero) (VL (wlit 7))) (VL wm8)) && range_known (s_facts st) kZP
            then fits_decided (s_facts st) zfree [sv_alu ALU_SUB R (sv_alu ALU_SUB (VP kZP wzero) SZ); sv_alu ALU_ADD (sv_alu ALU_SUB R (VP kZP wzero)) SZ;
                                                sv_alu ALU_ADD SZ (sv_alu ALU_SUB R (VP kZP wzero))] else false) eqn:C2.
  {
    change (sv_eqb R (sv_alu ALU_AND (sv_alu ALU_ADD (VP kZP wzero) (VL (wlit 7))) (VL wm8)) && range_known (s_facts st) kZP
            && fits_decided (s_facts st) zfree [sv_alu ALU_SUB R (sv_alu ALU_SUB (VP kZP wzero) SZ); sv_alu ALU_ADD (sv_alu ALU_SUB R (VP kZP wzero)) SZ;
                                                sv_alu ALU_ADD SZ (sv_alu ALU_SUB R (VP kZP wzero))] = true) in C2.
    apply andb_prop in C2 as [C2 FD]. apply andb_prop in C2 as [RQ RK]. apply sv_eqb_eq in RQ.

    unfold range_known in RK. destruct (find_range (s_facts st) kZP) as [[lo hi]|] eqn:FR; [|discriminate]. apply negb_true_iff in RK.
    pose proof (find_range_sound_gen E' (s_facts st) Pfacts kZP lo hi FR) as [_ ZH]. fold zp in ZPV. rewrite ZPV in ZH.
    assert (HI63 : w2Z hi < two63) by (unfold w2Z; rewrite RK; pose proof (int_range (wl hi)); unfold two63 in *; lia).

    assert (RV : bv_unsigned (den E' R) = align8 zp /\ zp <= align8 zp <= zp + 7 /\ align8 zp mod 8 = 0).
    { pose proof (align8_spec zp ltac:(lia)) as (A1 & A2 & A3). split; [| split; [exact A1| exact A2]].
      rewrite RQ, !den_sv_alu. cbn [alu64 alu]. rewrite bv_and_unsigned, bv_add_unsigned, (den_VP0 E' kZP wzero (weqb_refl _)), ZPV.
      cbn [den]. rewrite !wbv_unsigned, wlit_ok. change (to_Z 7%uint63) with 7.
      unfold wm8. rewrite wsub_ok, wzero_ok, wlit_ok. change ((0 - to_Z 8%uint63) mod two64) with (two64 - 2 ^ 3).
      rewrite wrap64, Z.mod_small by (unfold two64, two63 in *; lia). rewrite land_negpow2 by (unfold two64, two63 in *; lia).
      unfold align8. rewrite land_m8 by lia. reflexivity. }
    destruct RV as (RV & RB & RM).

    assert (FIT : align8 zp + sz <= zp + zf).
    { unfold fits_decided in FD. rewrite exists_lazy_eq in FD. pose proof (cand_vals E' R (VP kZP wzero) SZ) as (V1 & V2 & V3). cbv zeta in V1, V2, V3.
      rewrite RV, (den_VP0 E' kZP wzero (weqb_refl _)), ZPV in V1, V2, V3. fold sz in V1, V2, V3.
      assert (SMALL : (align8 zp - zp + sz) mod two64 = align8 zp - zp + sz) by (apply Z.mod_small; unfold two64; lia).
      rewrite SMALL in V1, V2, V3.
      cbn [existsb] in FD. rewrite orb_false_r in FD.
      repeat (apply orb_prop in FD as [FD|FD]);
        match type of FD with (match decide_ltu ?fs ?a ?b with _ => _ end) = true =>
          destruct (decide_ltu fs a b) as [[|]|] eqn:DF; try discriminate;
          pose proof (decide_ltu_sound E' (s_facts st) Pfacts _ _ _ DF) as LE; apply (proj1 (ltu_iff _ _ false)) in LE;
          rewrite Lzf' in LE; first [rewrite V1 in LE | rewrite V2 in LE | rewrite V3 in LE]; lia
        end. }
    assert (EQ : bv_unsigned (ev E' n) = align8 zp) by (rewrite EVn, <- DRR; exact RV).
    injection AP as <-. apply (FITS (align8 zp)); [lia| lia| exact EQ|].
    constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, <- DRR. reflexivity. }
    constructor.
    { cbn [fact_holds]. rewrite EQ. change (2 ^ to_Z 3%uint63) with 8. exact RM. }
    apply (zone_facts_sound E' n SZ (VP kZP wzero) zfree (align8 zp) _ EQ); rewrite ?(den_VP0 E' kZP wzero (weqb_refl _)), ?ZPV, ?Lzf'; fold sz; [lia| lia| unfold chunk_lo, chunk_hi, CHUNK_HDR in *; lia|].
    apply anchor_facts_sound; [exact Pfacts|]. rewrite ZPV, EQ. lia. }

  destruct R as [|kC oc| | | | | | | | |] eqn:ER; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C3; [|discriminate] end.
  apply andb_prop in C3 as [C3 WRO]. apply andb_prop in C3 as [C3 RNZ]. apply andb_prop in C3 as [C3 AL4].
  apply andb_prop in C3 as [C3 KCZ]. apply andb_prop in C3 as [OC KC0].
  apply (proj1 (weqb_ok _ _)) in OC. subst oc. apply negb_true_iff in KC0. apply negb_true_iff in KCZ.
  destruct (IMap.find kC (s_regs st)) as [rc|] eqn:FRC; [|discriminate].
  destruct (rg_hi rc) as [hlen| | | | | | | | | |] eqn:HRC; try discriminate.
  destruct (cell_at rc 0 8%uint63) as [hd|] eqn:CHD; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C4; [|discriminate] end.
  apply andb_prop in C4 as [C4 TEX]. apply andb_prop in C4 as [C4 SZ8].
  apply andb_prop in C4 as [C4 SZLE]. apply andb_prop in C4 as [C4 SZT]. apply andb_prop in C4 as [C4 SZ8192]. apply andb_prop in C4 as [C4 HDC0].
  apply andb_prop in C4 as [C4 NOA]. apply andb_prop in C4 as [C4 EXW]. apply andb_prop in C4 as [C4 WRC]. apply andb_prop in C4 as [HT LOC].
  apply negb_true_iff in HT. apply Uint63.eqb_correct in LOC. apply sv_eqb_eq in HDC0. subst hd. apply negb_true_iff in SZT.
  injection AP as <-.
  set (szw := wsub hlen (wlit 8%uint63)) in *.
  set (ourw := (VP kC wzero, VL hlen, VL (wlit 1%uint63))) in *.

  set (c := bv_unsigned (ev E' kC)).
  pose proof (Preg kC rc FRC) as ROC.
  pose proof (ro_range _ _ _ _ _ _ ROC KC0) as [RC1 RC2]. unfold loZ in RC1. rewrite LOC in RC1. unfold hiZ in RC2. rewrite HRC in RC2.
  cbn [den] in RC2. rewrite wbv_unsigned in RC2. fold c in RC1, RC2. change (keyZ 0%uint63) with 0 in RC1.
  assert (SZV : w2Z szw < two63) by (unfold w2Z; rewrite SZT; pose proof (int_range (wl szw)); unfold two63 in *; lia).
  unfold wleu in SZ8192. rewrite wltu_w2Z in SZ8192. apply negb_true_iff in SZ8192. apply Z.ltb_ge in SZ8192. rewrite wlit_ok in SZ8192.
  change (to_Z 8192%uint63) with 8192 in SZ8192.
  assert (E1 : w2Z szw = (w2Z hlen - 8) mod two64) by (subst szw; rewrite wsub_ok, wlit_ok; reflexivity).
  pose proof (w2Z_range hlen) as RHL.
  assert (HL1 : w2Z hlen = 8 + w2Z szw).
  { destruct (Z.lt_ge_cases (w2Z hlen) 8) as [LT8|GE8].
    - exfalso. rewrite E1 in SZV. unfold two64, two63 in *.
      replace (w2Z hlen - 8) with ((w2Z hlen - 8 + 18446744073709551616) + (-1) * 18446744073709551616) in SZV by lia.
      rewrite Z_mod_plus_full, Z.mod_small in SZV by lia. lia.
    - rewrite E1, Z.mod_small by (unfold two64 in *; lia). lia. }
  set (szd := w2Z szw) in *.

  destruct (decide_ltu (s_facts st) (VL szw) SZ) as [[|]|] eqn:DS; try discriminate.
  pose proof (decide_ltu_sound E' (s_facts st) Pfacts _ _ _ DS) as SLE. apply (proj1 (ltu_iff _ _ false)) in SLE.
  cbn [den] in SLE. rewrite wbv_unsigned in SLE. fold sz szd in SLE.

  assert (R8 : bv_unsigned (den E' (VP kC (wlit 8%uint63))) = c + 8).
  { rewrite den_VPu, wlit_ok. change (to_Z 8%uint63) with 8. fold c. apply Z.mod_small. lia. }
  assert (EQ : bv_unsigned (ev E' n) = c + 8) by (rewrite EVn, <- DRR; exact R8).

  assert (AL16 : c mod 16 = 0).
  { pose proof (find_align_sound_gen E' (s_facts st) Pfacts kC) as A. fold c in A. apply Uint63.leb_spec in AL4. change (to_Z 4%uint63) with 4 in AL4.
    pose proof (int_range (find_align (s_facts st) kC)).
    replace (2 ^ to_Z (find_align (s_facts st) kC)) with (16 * 2 ^ (to_Z (find_align (s_facts st) kC) - 4)) in A
      by (replace (to_Z (find_align (s_facts st) kC)) with (4 + (to_Z (find_align (s_facts st) kC) - 4)) at 2 by lia; rewrite Z.pow_add_r by lia; reflexivity).
    assert (PP : 0 < 2 ^ (to_Z (find_align (s_facts st) kC) - 4)) by (apply Z.pow_pos_nonneg; lia).
    apply Z.mod_divide in A; [|lia]. apply Z.mod_divide; [lia|]. destruct A as [q Hq]. exists (q * 2 ^ (to_Z (find_align (s_facts st) kC) - 4)). lia. }
  assert (CPOS : 0 < c /\ exists lo hi, find_range (s_facts st) kC = Some (lo, hi) /\ w2Z lo <= c <= w2Z hi /\ w2Z hi < two63).
  { unfold range_nz in RNZ. destruct (find_range (s_facts st) kC) as [[lo hi]|] eqn:FR; [|discriminate]. apply andb_prop in RNZ as [HH LNZ].
    apply negb_true_iff in HH. apply negb_true_iff in LNZ.
    pose proof (find_range_sound_gen E' (s_facts st) Pfacts kC lo hi FR) as [X1 X2]. fold c in X1, X2.
    assert (w2Z lo <> 0) by (intros X; rewrite weqb_eqb, X, wzero_ok in LNZ; discriminate).
    pose proof (w2Z_range lo). split; [lia|]. exists lo, hi. split; [reflexivity|]. split; [lia|].
    unfold w2Z. rewrite HH. pose proof (int_range (wl hi)). unfold two63 in *. lia. }
  destruct CPOS as (CPOS & rlo & rhi & FRC' & CRG & RHI).

  apply existsb_exists in EXW as (w0 & INW0 & EQW0). apply win3_eqb_eq in EQW0. subst w0.
  assert (OURDEN : wden E' ourw = Win c (w2Z hlen) 1).
  { subst ourw. unfold wden. rewrite (den_VP0 E' kC wzero (weqb_refl _)). fold c. cbn [den]. rewrite !wbv_unsigned, wlit_ok. reflexivity. }
  assert (INLB : In (c, w2Z hlen) LB).
  { pose proof (proj1 (Forall_forall _ _) WF (wden E' ourw) (in_map _ _ _ INW0)) as (_ & _ & _ & [[K _]|[[_ B]|[K _]]]);
      rewrite OURDEN in *; cbn [w_kind w_iv w_lo w_len] in *; [unfold K_STACK in K; lia| exact B| unfold K_SUB in K; lia]. }
  assert (DISJ : forall b, In b (owned g) -> forall a, c <= a < c + w2Z hlen -> ~ in_iv b a).
  { intros b Hb a Ha. destruct (proj1 (Forall_forall _ _) Wk (wden E' ourw) (in_map _ _ _ INW0) ltac:(rewrite OURDEN; cbn [w_kind]; unfold K_STACK; lia)) as [[_ D]|[NB _]].
    - apply (D b Hb a). rewrite OURDEN. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha.
    - rewrite OURDEN in NB. cbn [w_kind] in NB. exfalso. exact (NB eq_refl). }
  assert (RDISJ : forall b, In b (owned g) -> rdisj c (w2Z hlen) (fst b) (snd b)).
  { intros b Hb. pose proof (owned_pos g P b Hb) as BP. unfold rdisj.
    destruct (Z.le_gt_cases (c + w2Z hlen) (fst b)); [left; assumption|]. destruct (Z.le_gt_cases (fst b + snd b) c); [right; assumption|].
    exfalso. destruct (Z.le_gt_cases c (fst b)).
    - apply (DISJ b Hb (fst b)); [lia|]. unfold in_iv. lia.
    - apply (DISJ b Hb c); [lia|]. unfold in_iv. lia. }

  assert (FD : Forall (chunk_disj (c, szd)) (z_chunks (u_zone g))).
  { apply Forall_forall. intros ch Hch. pose proof (RDISJ (chunk_block ch) (owned_chunk g ch Hch)) as D.
    unfold chunk_disj, chunk_block, rdisj, CHUNK_HDR in *. cbn [fst snd] in D |- *. lia. }
  pose proof (zalloc_fresh_ok (u_zone g) c szd 0 ZV CPOS AL16 ltac:(unfold CHUNK_SIZE0; lia) ltac:(lia) FD) as ZF.
  cbv zeta in ZF. destruct ZF as (ZV' & FST & _ & PTR' & _ & _ & CH').
  set (z' := snd (zalloc_fresh (u_zone g) c szd 0)) in *.
  assert (ZG : zone_grows (u_zone g) z') by (subst z'; apply zone_grows_fresh; [exact ZV| lia]).
  assert (ZPTR' : z_ptr z' = c + 8) by (rewrite <- PTR', FST; unfold CHUNK_HDR; lia).
  assert (ZFREE' : z_free z' = szd) by (subst z'; unfold zalloc_fresh, zone_bump, zone_expand; cbn; lia).
  assert (ZHEAD' : z_head z' = c) by (unfold z_head; rewrite CH'; reflexivity).
  set (g' := mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) (u_levels g) (u_cstk g) (u_vstk g) z').

  set (ws0 := List.filter (fun w => negb (win3_eqb w ourw)) ws) in *.
  set (neww := (VP n wzero, SZ, VL (wlit 5%uint63))) in *.
  assert (SUB0 : forall w, In w ws0 -> In w ws /\ w <> ourw).
  { intros w Hw. apply filter_In in Hw as [Hw NS]. split; [exact Hw|]. intros ->. rewrite win3_eqb_refl in NS. discriminate. }
  assert (LEN' : Z.of_nat (length (ws0 ++ [neww])) < two63).
  { rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w ourw)) ws). subst ws0. unfold two63. lia. }
  assert (NEWDEN : wden E' neww = Win (c + 8) sz 5).
  { subst neww. unfold wden. rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ. fold sz. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }

  assert (OTHERS : forall x, In x ws -> x <> ourw -> w_kind (wden E' x) <> K_STACK -> forall a, in_iv (w_iv (wden E' x)) a -> ~ (c <= a < c + w2Z hlen)).
  { intros x Hx NX NK a Ha Hc.
    pose proof (proj1 (forallb_forall _ _) WRO x Hx) as WR. pose proof (proj1 (forallb_forall _ _) NOA x Hx) as NO. cbn beta in NO.
    destruct x as [[xa xb] xc]. unfold win_region_ok in WR.
    destruct xc as [kd| | | | | | | | | |]; try discriminate WR.
    assert (KDV : w_kind (wden E' (xa, xb, VL kd)) = w2Z kd) by (cbn [wden w_kind den]; apply wbv_unsigned).
    apply andb_prop in WR as [T0 WR]. apply negb_true_iff in T0.
    apply orb_prop in WR as [K0'|WR]; [apply Uint63.eqb_correct in K0'; rewrite KDV in NK; unfold w2Z in NK; rewrite T0, K0' in NK; exfalso; apply NK; reflexivity|].
    apply orb_prop in WR as [GH|WR].
    { pose proof (aw_ghost_apart segs IMGX AW _ _ _ _ _ HA) as GA.
      refine (GA _ _ (in_map (wden E') _ _ Hx) (in_map (wden E') _ _ INW0) _ _ a Ha _).
      - rewrite KDV. unfold K_GHOST, w2Z. rewrite T0. apply Uint63.leb_spec in GH. change (to_Z 7%uint63) with 7 in GH. lia.
      - rewrite OURDEN. reflexivity.
      - rewrite OURDEN. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Hc. }
    destruct xa as [|k ko| | | | | | | | |]; try discriminate WR.
    apply andb_prop in WR as [WR0 WR]. apply andb_prop in WR0 as [O0 KK0]. apply (proj1 (weqb_ok _ _)) in O0. subst ko. apply negb_true_iff in KK0.
    destruct (IMap.find k (s_regs st)) as [rk|] eqn:FK; [|discriminate].
    apply andb_prop in WR as [LK HK]. apply Uint63.eqb_correct in LK.

    apply orb_prop in NO as [NE|EQO]; [| apply win3_eqb_eq in EQO; exact (NX EQO)].
    apply negb_true_iff in NE. apply Uint63.eqb_false_correct in NE.
    unfold wden, w_iv in Ha. rewrite (den_VP0 E' k wzero (weqb_refl _)) in Ha. cbn [den w_lo w_len fst snd] in Ha. unfold in_iv in Ha. cbn [fst snd] in Ha.
    destruct (PrimInt63.eqb (wl kd) 1%uint63) eqn:KD1.
    -
      apply Uint63.eqb_correct in KD1.
      destruct (decide_ltu (s_facts st) (VL wzero) (rg_hi rk)) as [[|]|] eqn:DH; try discriminate HK.
      pose proof (decide_ltu_sound E' (s_facts st) Pfacts _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS.
      cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS.
      pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx)) as WFx.
      assert (K1 : w_kind (wden E' (VP k wzero, xb, VL kd)) = K_BLOCK) by (rewrite KDV; unfold w2Z; rewrite T0, KD1; reflexivity).
      destruct WFx as (_ & _ & _ & [[KS _]|[[_ INx]|[KS _]]]);
        [rewrite K1 in KS; unfold K_STACK, K_BLOCK in KS; clear - KS; lia| | rewrite K1 in KS; unfold K_SUB, K_BLOCK in KS; clear - KS; lia].
      unfold w_iv, wden in INx. cbn [w_lo w_len] in INx. rewrite (den_VP0 E' k wzero (weqb_refl _)) in INx.
      destruct (Z.eq_dec (bv_unsigned (ev E' k)) c) as [EQX|NEX].
      + apply (Pdisj k rk kC rc FK FRC NE KK0 KC0 (or_intror WRC) c). unfold loZ, hiZ. rewrite LK, EQX, LOC, HRC. cbn [den]. rewrite wbv_unsigned.
        change (keyZ 0%uint63) with 0. fold c. clear - HPOS HL1 SZ8192. lia.
      + exact (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ a HA INx INLB ltac:(cbn [fst]; exact NEX)
                 ltac:(unfold in_iv; cbn [fst snd]; exact Ha) ltac:(unfold in_iv; cbn [fst snd]; exact Hc)).
    -
      apply sv_eqb_eq in HK.
      apply (Pdisj k rk kC rc FK FRC NE KK0 KC0 (or_intror WRC) a). split.
      + unfold loZ, hiZ. rewrite LK, HK. change (keyZ 0%uint63) with 0. lia.
      + unfold loZ, hiZ. rewrite LOC, HRC. cbn [den]. rewrite wbv_unsigned. change (keyZ 0%uint63) with 0. fold c. lia. }

  assert (MATC : forall a, c <= a < c + w2Z hlen -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. destruct (ro_valid _ _ _ _ _ _ ROC KC0 a) as (RB & WB & NS).
    - unfold loZ, hiZ. rewrite LOC, HRC. cbn [den]. rewrite wbv_unsigned. change (keyZ 0%uint63) with 0. fold c. lia.
    - split; [| exact NS]. specialize (WB WRC). unfold wb, wview in WB.
      destruct (ms_mem ms (Z_to_bv 64 a)) as [b|] eqn:MB; [congruence|].
      rewrite Z_to_bv_unsigned in WB. replace (bv_wrap 64 a) with a in WB by (symmetry; apply bv_wrap_small; rewrite bv_modulus_64; lia).
      rewrite NS in WB. discriminate. }

  apply setreg_sound; [| exact RNX| transitivity (den E' R); [reflexivity|]; rewrite ER, DRR, <- EVn; apply bv_eq; rewrite (den_VP0 E' n wzero (weqb_refl _)); reflexivity].
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kC] [(n, new_region SZ)] _ _ (PrimInt63.add n 1)).
  - intros k [<-|[]]. split; [exact KC0|]. exists rc. auto.
  - constructor; [intros []| constructor].
  - intros k r [H|[]]. injection H as <- <-. exact NZ.
  - intros k r [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n (new_region SZ) NZ).
    + exact I.
    + reflexivity.
    + rewrite LOZN, EQ. lia.
    + rewrite HIZN, EQ. lia.
    + intros a Ha. rewrite LOZN, HIZN, EQ in Ha. apply MATC. lia.
    + intros gk gr F. cbn [new_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  -
    intros k r a [H|[]] IR. injection H as <- <-. right. exists kC, rc. split; [left; reflexivity|]. split; [exact FRC|].
    unfold inR in IR |- *. rewrite LOZN, HIZN, EQ in IR. unfold loZ, hiZ. rewrite LOC, HRC. cbn [den]. rewrite wbv_unsigned. change (keyZ 0%uint63) with 0. fold c. lia.
  - intros k1 r1 k2 r2 a [X1|[]] [X2|[]] NE12. injection X1 as <- <-. injection X2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E' aw), (map (wden E') (ws0 ++ [neww])),
           (map (den E') [root; cb; ce; ccap; vb; ve; vcap; VP n wzero; VL szw; VP kC wzero; slot; tD; restD; rootT; n1; P1; zh]), LB.
    split; [apply mk_args_sound; exact LEN'|].

    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E' 1 g LB ws (ws0 ++ [neww]) P O Wk);
            [intros x Hx; apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact (proj1 (SUB0 x Hx))| right; left; subst neww; apply UOK.kind_sub; vm_compute; reflexivity]
            |intros x Hx; destruct (win3_eqb x ourw) eqn:QK1;
             [right; right; apply win3_eqb_eq in QK1; subst x; rewrite OURDEN; cbn [w_kind w_iv w_lo w_len]; split; [reflexivity|]; split; [exact INLB|];
              unfold c24, C24_LO, C24_HI; clear - HL1 SZ8192; lia
             |left; apply in_or_app; left; subst ws0; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1; reflexivity]]|]. split.
    + unfold windows_wf in *. rewrite map_app. apply Forall_app. split.
      * apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). exact (proj1 (Forall_forall _ _) WF (wden E' x) (in_map _ _ _ (proj1 (SUB0 x Hx)))).
      * constructor; [|constructor]. rewrite NEWDEN. unfold window_wf. cbn [w_lo w_len w_kind w_iv].
        split; [lia|]. split; [lia|]. split; [lia|]. right; right. split; [unfold K_SUB; lia|].
        exists (c, w2Z hlen). split; [exact INLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. lia.
    + cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
      exists g'. split; [| split; [| split; [| split; [| split]]]].
      *
        unfold link. cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
        change (u_root g') with (u_root g). change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g).
        change (u_zone g') with z'. change (u_levels g') with (u_levels g). change (u_cur_slot g') with (u_cur_slot g).
        split; [exact Lroot|]. split; [exact Lcb|]. split; [exact Lce|]. split; [exact Lccap|]. split; [exact Lvb|]. split; [exact Lve|]. split; [exact Lvcap|].
        split; [rewrite ZPTR', (den_VP0 E' n wzero (weqb_refl _)), EQ; reflexivity|].
        split; [rewrite ZFREE'; cbn [den]; rewrite wbv_unsigned; reflexivity|].
        split; [rewrite ZHEAD', (den_VP0 E' kC wzero (weqb_refl _)); reflexivity|].
        exact LD.
      *
        unfold pure_ok. change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_zone g') with z'.
        change (u_levels g') with (u_levels g). change (u_D g') with (u_D g).
        pose proof P as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
        split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|]. split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
        split; [exact Q9|]. split; [exact Q10|]. split; [exact (levels_alloc_mono_zone _ _ _ ZG Q11)| exact ZV'].
      *
        destruct O as [O1 [O2 OT]]. unfold own_ok, owned. change (u_zone g') with z'. rewrite CH'. cbn [map].
        change (cstk_block g') with (cstk_block g). change (vstk_block g') with (vstk_block g).
        assert (NB : chunk_block (c, szd) = (c, w2Z hlen)) by (unfold chunk_block, CHUNK_HDR; cbn [fst snd]; f_equal; lia).
        rewrite NB. split; [| split; [| exact OT]].
        -- intros b [<-|[<-|[<-|Hb]]]; [apply O1; left; reflexivity| apply O1; right; left; reflexivity| exact INLB| apply O1; right; right; exact Hb].
        -- unfold owned in O2. inversion O2 as [|x l F1 P2]; subst. inversion P2 as [|x' l' F2 P3]; subst.
           assert (RS : forall b, In b (owned g) -> rdisj (fst b) (snd b) c (w2Z hlen)).
           { intros b Hb. pose proof (RDISJ b Hb). unfold rdisj in *. lia. }
           constructor; [| constructor; [| constructor; [| exact P3]]].
           ++ apply Forall_cons_iff in F1 as [F1a F1b]. constructor; [exact F1a| constructor; [exact (RS _ (owned_cstk g))| exact F1b]].
           ++ constructor; [exact (RS _ (owned_vstk g))| exact F2].
           ++ apply Forall_forall. intros b Hb. cbn [fst snd]. apply RDISJ. right; right. exact Hb.
      *
        unfold wins_ok in *. rewrite map_app. apply Forall_app. split.
        -- apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx). destruct (SUB0 x Hx) as [Hx0 NX].
           destruct (proj1 (Forall_forall _ _) Wk (wden E' x) (in_map _ _ _ Hx0) NS) as [[KDJ D]|[NB SO]].
           ++ left. split; [exact KDJ|]. intros b Hb a Ha. unfold owned in Hb. change (u_zone g') with z' in Hb. rewrite CH' in Hb. cbn [map] in Hb.
              change (cstk_block g') with (cstk_block g) in Hb. change (vstk_block g') with (vstk_block g) in Hb.
              destruct Hb as [<-|[<-|[<-|Hb]]]; [exact (D _ (owned_cstk g) a Ha)| exact (D _ (owned_vstk g) a Ha)| | exact (D b (or_intror (or_intror Hb)) a Ha)].
              intros Hin. apply (OTHERS x Hx0 NX NS a Ha). unfold in_iv, chunk_block, CHUNK_HDR in Hin. cbn [fst snd] in Hin. lia.
           ++ right. split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *.
              change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_levels g') with (u_levels g). change (u_zone g') with z'.
              destruct SO as [A|[A|[A|(KK & _)]]]; [left; exact A| right; left; exact A| right; right; left; exact A|].
              exfalso. exact (N5 _ (in_map _ _ _ Hx0) KK).
        -- constructor; [|constructor]. intros _. right. rewrite NEWDEN. split; [cbn [w_kind]; unfold K_BLOCK; lia|].
           unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; right; right. split; [reflexivity|].
           change (u_zone g') with z'. rewrite ZPTR', CH'. cbn [hd]. unfold chunk_hi, CHUNK_HDR. cbn [fst snd]. lia.
      *
        destruct M as (M1 & M2 & M3 & M4 & M5 & M6).
        unfold mem_ok. cbv zeta. change (u_levels g') with (u_levels g). change (u_zone g') with z'. change (u_root g') with (u_root g).
        change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g).
        split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [| split; [exact M5|]].
        -- rewrite CH'. cbn [chunks_at]. split; [| exact M4].
           rewrite EH. cbn [fst].
           destruct (cell_at_u64 segs (s_priv st) E' (ms_mem ms) kC rc 0 c0 ROC KC0 ltac:(lia) ltac:(unfold two62Z; lia) CHD) as (U & _ & _).
           rewrite Z.add_0_r in U. fold c in U. rewrite <- Lc0 in U. unfold z_head in U. rewrite EH in U. exact U.
        -- intros l Hl i Hi. destruct (M6 l Hl i Hi) as (ox & T & CS & BS). exists ox. split; [| split].
           ++ eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T].
           ++ intros c1 Hc1. destruct (CS c1 Hc1) as [A U]. split; [exact (proj2 ZG _ _ A)| exact U].
           ++ unfold bodies_ok in *. eapply Forall_impl; [| exact BS]. intros r (R0 & A & U). split; [exact R0|]. split; [exact (proj2 ZG _ _ A)| exact U].
      *
        split; [intros X; discriminate|].
        destruct CS0 as (_ & ((X & A) & PTU) & SE). split.
        { split.
          { exists X. change (u_levels g') with (u_levels g). change (u_zone g') with z'.
            eapply Acct.acct_frame; [| exact A]. intros l i ox Hl Hi T.
            eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T]. }

          intros MD1. destruct (PTU MD1) as (S0 & KP0 & PA0). exists S0. change (u_levels g') with (u_levels g). change (u_zone g') with z'. split.
          - apply (Pot.Pot.kids_pk_frame (bmem_of segs (ms_mem ms)) (bmem_of segs (ms_mem ms)) (u_zone g) z' (u_levels g) S0); [| exact KP0]. intros l i ox Hl Hi T.
            eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T].
          - apply (pot_at_ws _ _ _ PA0). apply UOK.pot_map_old. intros x Hx.
            apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact (proj1 (SUB0 x Hx))| right; subst neww; apply kind_ne; vm_compute; reflexivity]. }

        change (u_zone g') with z'. rewrite CH'. rewrite map_app.
        apply SealX.seal_ok_app_other; [| intros w [<-|[]]; rewrite NEWDEN; cbn [w_kind]; unfold Seal.K_TWIN; lia].
        assert (HLP : 0 < w2Z hlen) by (clear - HL1 SZ8192 SZV; pose proof (w2Z_range szw); lia).
        apply Seal.seal_ok_cons.
        -- apply (SealX.seal_ok_map _ _ _ _ _ SE). intros x Hx. left. exact (proj1 (SUB0 x Hx)).
        -- cbn [snd]. apply Uint63.eqb_correct in SZ8. apply (f_equal to_Z) in SZ8. rewrite land_spec' in SZ8.
           change (to_Z 7%uint63) with (Z.ones 3) in SZ8. change (to_Z 0%uint63) with 0 in SZ8. rewrite Z.land_ones in SZ8 by lia. change (2 ^ 3) with 8 in SZ8.
           subst szd. unfold w2Z. fold szw. rewrite SZT. exact SZ8.
        -- cbn [fst]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
           apply (GSeal.twins_explained_sound E' st kC rc [cb; vb] ws Pfacts Pdisj FRC KC0 WRC); try assumption.
           ++ unfold loZ. rewrite LOC. reflexivity.
           ++ unfold hiZ. rewrite HRC. cbn [den]. rewrite wbv_unsigned. exact HLP.
           ++ fold c. clear - AL16. rewrite (Z.div_mod c 16) by lia. rewrite AL16. replace (16 * (c / 16) + 0) with ((2 * (c / 16)) * 8) by lia. apply Z.mod_mul. lia.
           ++ fold c. intros v [<-|[<-|[]]].
              ** rewrite <- Lcb. split; [exact (proj2 (proj2 (proj2 VC)))|]. pose proof (RDISJ _ (owned_cstk g)) as D. pose proof (owned_pos g P _ (owned_cstk g)) as PO.
                 unfold rdisj in D. cbn [fst snd cstk_block] in D, PO. lia.
              ** rewrite <- Lvb. split; [exact (proj2 (proj2 (proj2 VV)))|]. pose proof (RDISJ _ (owned_vstk g)) as D. pose proof (owned_pos g P _ (owned_vstk g)) as PO.
                 unfold rdisj in D. cbn [fst snd vstk_block] in D, PO. lia.
           ++ apply in_map. exact (proj1 (SUB0 x Hx)).
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') (ws0 ++ [neww])) _ a (mk_args_sound E' 1%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
    rewrite map_app in NW. split.
    + destruct (in_ws_dec (map (wden E') ws) a) as [IN|NIN].
      * right. exists kC, rc. split; [left; reflexivity|]. split; [exact FRC|].
        apply in_ws_map_iff in IN as (x & Hx & Ha).
        destruct (win3_eqb x ourw) eqn:ISW.
        -- apply win3_eqb_eq in ISW. subst x. rewrite OURDEN in Ha. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha.
           unfold inR, loZ, hiZ. rewrite LOC, HRC. cbn [den]. rewrite wbv_unsigned. change (keyZ 0%uint63) with 0. fold c. lia.
        -- exfalso. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. apply in_ws_map_iff.
           exists x. split; [| exact Ha]. apply filter_In. split; [exact Hx|]. rewrite ISW. reflexivity.
      * left. exact (FPold a RA NI NIN).
    + intros k r [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
      cbn [map]. rewrite NEWDEN. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
      unfold inR in IR. rewrite LOZN, HIZN, EQ in IR. lia.
  -
    constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, <- DRR. reflexivity. }
    constructor.
    { cbn [fact_holds]. rewrite EQ. change (2 ^ to_Z 3%uint63) with 8. apply Z.mod_divide; [lia|]. apply Z.mod_divide in AL16; [|lia].
      destruct AL16 as [q Hq]. exists (2 * q + 1). lia. }
    apply (zone_facts_sound E' n SZ (VP n wzero) (VL szw) (c + 8) _ EQ);
      [ rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ; lia
      | rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ; cbn [den]; rewrite wbv_unsigned; fold sz szd; lia
      | rewrite (den_VP0 E' n wzero (weqb_refl _)), EQ; cbn [den]; rewrite wbv_unsigned; fold szd; lia |].
    apply anchor_facts_sound; [exact Pfacts|]. fold c. rewrite EQ. lia.
Qed.

Theorem g4a_sound : contract_sound segs OPS MP PB g4a_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g4a_contract c_apply] in HAP.
  destruct (g4a_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. destruct (g4a_sound_main E st ms model st' HS AP) as (E' & HX & HS').
       exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS'). }
  all: exfalso; unfold g4a_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G4A.
