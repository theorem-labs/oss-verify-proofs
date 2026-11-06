(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.B10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac addr_near k ::=
  let inb := eval vm_compute in (andb (Z.leb 0 k) (Z.ltb k 4608))%Z in
  lazymatch inb with true => idtac end.

(* [comment removed for export] *)
Definition hid (P : Prop) : Prop := P.
Ltac hide H := let T := type of H in change (hid T) in H.
Ltac unhide_all := unfold hid in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma signed_lit64 : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_signed. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. Qed.

Lemma sxb_small : forall b : byte, bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b Hb. unfold sxb. f_equal. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256.
  rewrite Z.mod_small; lia.
Qed.

Lemma land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = 32 * (x / 32).
Proof.
  intros x Hx. change 18446744073709551584 with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5) with 32. lia.
Qed.
(* [comment removed for export] *)
Ltac fix_land32 :=
  repeat match goal with
  | |- context [Z.land ?x 18446744073709551584] =>
      first [ replace (Z.land x 18446744073709551584) with x by (rewrite land_m32 by lia; Z.div_mod_to_equations; lia)
            | replace (Z.land x 18446744073709551584) with (x + -16) by (rewrite land_m32 by lia; Z.div_mod_to_equations; lia) ]
  end.

(* [comment removed for export] *)
Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2^64). rewrite <- Znumtheory.Zmod_div_mod; [reflexivity| lia| lia| exists (2^56); reflexivity].
Qed.
Ltac sb_fix := lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) => rewrite (le1_lit z); mem_after_store
  end.

(* [comment removed for export] *)
Lemma unsigned_lit_neg : forall e, - 2^63 <= e < 0 -> bv_unsigned (Z_to_bv 64 e) = e + 2^64.
Proof.
  intros e He. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite <- (Z.mod_add e 1 (2^64)) by lia. apply Z.mod_small. lia.
Qed.

Ltac cnorm :=
  unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
  change (bv_unsigned (Z_to_bv 64 0)) with 0;
  fold_lit_ux;
  repeat match goal with
  | |- context [Z.land ?x 7] => rewrite (land7 x) by flia
  end;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] => first [ rewrite (inr64_unsigned_lit e) by zrange | rewrite (unsigned_lit_neg e) by flia ]
  | |- context [bv_signed (Z_to_bv 64 ?e)] => rewrite (signed_lit64 e) by flia
  end.
Ltac brT := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with true; [cbv iota| symmetry; cnorm; solve_cond_rec] end.
Ltac brF := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  replace c with false; [cbv iota| symmetry; cnorm; solve_cond_rec] end.
Ltac br := first [brT | brF].
Ltac brfork H := if_cases H; zify_cond H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation mem := (word -> option byte).

Lemma acc_read1 : forall (m : mem) a n x, acc asegs m a n -> a <= x < a + n ->
  exists b, ov_read_bytes asegs m (wa (shad x)) 1 = Some [b] /\ sh_ok b x.
Proof.
  intros m a n x H Hx. destruct (H (x - a) ltac:(lia)) as (b & Hb & Hok).
  replace (a + (x - a)) with x in * by lia. exists b. split; [| exact Hok].
  pose proof (bytes_at_ov_read asegs m (shad x) [b] 0 1 Hb ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

(* [comment removed for export] *)
Definition shk (m : mem) (b : byte) (X : Z) : Prop := bytes_at asegs m (shad X) [b].

Lemma acc_shk : forall (m : mem) a n x, acc asegs m a n -> a <= x < a + n -> exists b, shk m b x.
Proof.
  intros m a n x H Hx. destruct (H (x - a) ltac:(lia)) as (b & Hb & _).
  replace (a + (x - a)) with x in * by lia. exists b. exact Hb.
Qed.
Lemma shk_read : forall (m : mem) b X, shk m b X -> ov_read_bytes asegs m (wa (shad X)) 1 = Some [b].
Proof.
  intros m b X Hb. pose proof (bytes_at_ov_read asegs m (shad X) [b] 0 1 Hb ltac:(cbn; lia)) as R.
  rewrite Z.add_0_r in R. exact R.
Qed.

Lemma shk_ok : forall (m : mem) a n X sz b, acc asegs m a n -> shk m b X -> a <= X -> X + sz <= a + n -> 0 < sz ->
  X mod 8 + sz - 1 < 8 -> 0 <= X -> sh_ok b (X + sz - 1).
Proof.
  intros m a n X sz b H K H1 H2 H3 H4 H5. destruct (acc_read1 m a n (X + sz - 1) H ltac:(lia)) as (b' & R & OK).
  assert (E : shad (X + sz - 1) = shad X) by (unfold shad; Z.div_mod_to_equations; lia).
  rewrite E in R. rewrite (shk_read m b X K) in R. injection R as <-. exact OK.
Qed.

(* [comment removed for export] *)
Lemma sh_ok_cases : forall b Y, sh_ok b Y -> bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ Y mod 8 < bv_unsigned b).
Proof. intros b Y H. exact H. Qed.
Lemma sh_ok_8 : forall b X, sh_ok b (X + 8 - 1) -> X mod 8 = 0 -> bv_unsigned b = 0.
Proof. intros b X [H|[H1 H2]] H8; [exact H|]. exfalso. revert H2. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Ltac next_instr k :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
      lazymatch fw with
      | Some ?w => let d := eval vm_compute in (decode_any w) in
                   lazymatch d with Some (?i, _) => k i | _ => fail "undecodable" end
      | _ => fail "no instruction"
      end
  end.
Ltac instr_at segs pc k :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w => let d := eval vm_compute in (decode_any w) in
               lazymatch d with Some (?i, _) => k i | _ => fail "undecodable" end
  | _ => fail "no instruction"
  end.

(* [comment removed for export] *)
Ltac reg_val r k :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key r) in
      let v := eval cbv beta iota delta [tget mkR] in (tget p R) in
      lazymatch v with Some ?x => k x end
  end.

(* [comment removed for export] *)
Ltac shadow_base E :=
  lazymatch E with
  | (?X ≫ 3 + 2147450880)%Z => X
  | (?X ≫ 3 + SHB)%Z => X
  | (SHB + ?X ≫ 3)%Z => X
  | (2147450880 + ?X ≫ 3)%Z => X
  | (?X / 8 + 2147450880)%Z => X
  | (?X / 8 + SHB)%Z => X
  | Zpos _ => let x := eval vm_compute in ((E - 2147450880) * 8)%Z in x      (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Ltac shload :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | Load SZ1 _ _ ?rs ?imm =>
        reg_val rs ltac:(fun v =>
          lazymatch v with
          | Z_to_bv 64 ?E =>
              let X := shadow_base E in
              lazymatch goal with
              | |- evt _ _ (MS _ _ _ _ _ ?m _) =>
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        let b := fresh "shb" in let K := fresh "SHK" in
                        destruct (acc_shk m a n X ACC ltac:(lia)) as (b & K);
                        let HR2 := fresh "SHL" in
                        assert (HR2 : ov_read_bytes asegs m (Z_to_bv 64 E) 1 = Some [b])
                          by (rewrite <- (shk_read m b X K); f_equal; unfold wa, shad, SHB; f_equal;
                              rewrite ?Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia)
                    end
                  | fail 1 "shload: no acc fact covers" X ]
              end
          end)
    end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma shad_range : forall x, 0 <= x < 2^47 -> 2147450880 <= shad x < 17594333495296.
Proof. intros x Hx. unfold shad, SHB. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Lemma acc_write_out : forall (m : mem) a bs A N (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  acc asegs m A N -> 0 <= A -> A + N <= 2^47 -> (a + n <= 2147450880 \/ 17594333495296 <= a) ->
  acc asegs (write_to_mem m (wa a) bs) A N.
Proof.
  intros m a bs A N n Hn Ha Hl H HA HN Hd i Hi. destruct (H i Hi) as (b & Hb & OK). exists b. split; [| exact OK].
  apply (bytes_at_write_other_n asegs m a bs _ _ n Hn Ha Hl Hb). cbn [length]. pose proof (shad_range (A + i) ltac:(lia)). lia.
Qed.
(* [comment removed for export] *)
Lemma acc_write_gen : forall (m : mem) a bs A N (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  acc asegs m A N -> 0 <= A -> (a + n <= shad A \/ shad (A + N) < a) ->
  acc asegs (write_to_mem m (wa a) bs) A N.
Proof.
  intros m a bs A N n Hn Ha Hl H HA Hd i Hi. destruct (H i Hi) as (b & Hb & OK). exists b. split; [| exact OK].
  apply (bytes_at_write_other_n asegs m a bs _ _ n Hn Ha Hl Hb). cbn [length].
  assert (shad A <= shad (A + i) <= shad (A + N)) by (unfold shad; Z.div_mod_to_equations; lia). lia.
Qed.
Lemma shk_write : forall (m : mem) a bs b X (n : Z),
  Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  shk m b X -> (a + n <= shad X \/ shad X < a) -> shk (write_to_mem m (wa a) bs) b X.
Proof.
  intros m a bs b X n Hn Ha Hl H Hd. apply (bytes_at_write_other_n asegs m a bs _ _ n Hn Ha Hl H). cbn [length]. lia.
Qed.

Ltac lept_transport_extra m a bs n Hn Ha Hl :=
  repeat match goal with
  | H : acc asegs m ?A ?N |- _ =>
      first [ apply (acc_write_out m a bs A N n Hn Ha Hl) in H; [ | tlia | tlia | tlia ]
            | apply (acc_write_gen m a bs A N n Hn Ha Hl) in H; [ | tlia | unfold shad, SHB; Z.div_mod_to_equations; tlia ]
            | idtac "note: dropping acc fact (store may alias its shadow):" H; clear H ]
  | H : shk m ?b ?X |- _ =>
      first [ apply (shk_write m a bs b X n Hn Ha Hl) in H; [ | unfold shad, SHB; Z.div_mod_to_equations; tlia ]
            | clear H ]
  end.
Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= lept_transport_extra m a bs n Hn Ha Hl.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bvmap_set_same_eq : forall (R : bvmap 5 word) r v, reg_get R r = v -> r <> Z_to_bv 5 0 -> True.
Proof. intros. exact I. Qed.

(* [comment removed for export] *)
Ltac norm_regset :=
  repeat match goal with
  | |- context [@bvmap_set 5 word ?r ?v ?R] =>
      let p := eval vm_compute in (bv_key r) in
      change (@bvmap_set 5 word r v R) with (tset p v R);
      cbv beta iota delta [tset mkR]
  end.

(* [comment removed for export] *)
Ltac bstep := lstep; try br.
Ltac bsteps_to p := repeat (tryif at_pc p then fail else bstep).

Ltac shbyte_of c :=
  lazymatch c with
  | context [sxb ?b] => b
  | context [@bv_unsigned 8 ?b] => b
  end.


(* [comment removed for export] *)
Ltac shbr_merge ru FAST OK :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u' : word,
                 ms' = MS (@bvmap_set 5 word ru u' R) F (Z_to_bv 64 FAST) fc rv m ro));
      [ destruct OK as [OK|[OK ?]];
        [ (* [comment removed for export] *)
          brF; apply evt_done;
          lazymatch goal with |- exists u', _ = MS (@bvmap_set 5 word ?r u' ?R') _ _ _ _ _ _ =>
            let p := eval vm_compute in (bv_key r) in
            let v := eval cbv beta iota delta [tget mkR] in (tget p R') in
            lazymatch v with Some ?x => exists x end end;
          norm_regset; reflexivity
        | (* [comment removed for export] *)
          brT; bsteps_to FAST; apply evt_done; eexists; norm_regset; reflexivity ]
      | let u' := fresh "u" in let E := fresh "E" in let ms := fresh "ms" in
        intros ms (u' & E); subst ms; norm_regset; clear OK ]
  end.

(* [comment removed for export] *)
Ltac shbr :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?SLOW else Z_to_bv 64 ?FAST) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          instr_at segs SLOW ltac:(fun i =>
            lazymatch i with
            | OpImm ALU_AND ?ru _ _ =>
                (* [comment removed for export] *)
                let szm1 := constr:(0%Z) in
                let S4 := eval vm_compute in (SLOW + 4)%Z in
                instr_at segs S4 ltac:(fun i2 =>
                  let szm1 := lazymatch i2 with
                              | OpImm ALU_ADD _ _ ?imm => eval vm_compute in (bv_unsigned imm)
                              | _ => constr:(0%Z) end in
                  let sz := eval vm_compute in (szm1 + 1)%Z in
                  let OK := fresh "SHOK" in
                  first [
                    match goal with
                    | ACC : acc asegs m ?a ?n |- _ =>
                        assert (OK : sh_ok b (X + sz - 1)) by (apply (shk_ok m a n X sz b ACC K); lia)
                    end
                  | fail 1 "shbr: cannot prove the access addressable:" X sz ];
                  let BB := fresh "BB" in
                  assert (BB : 0 <= bv_unsigned b < 8)
                    by (pose proof (bv_unsigned_in_range 8 b); destruct OK as [?|[? ?]]; lia);
                  rewrite ?(sxb_small b) by lia;
                  shbr_merge ru FAST OK; clear K BB)
            | _ =>
                (* [comment removed for export] *)
                let OK := fresh "SHOK" in
                first [
                  match goal with
                  | ACC : acc asegs m ?a ?n |- _ =>
                      assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr: cannot prove the 8-byte access addressable:" X ];
                apply sh_ok_8 in OK; [ | lia ];
                rewrite ?(sxb_small b) by lia;
                brF; clear K OK
            end)
      | _ => fail "shbr: no shk fact for" b
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac shnorm :=
  repeat match goal with
  | |- context [Z.shiftr ?x ?k] => is_Zlit k; rewrite (Z.shiftr_div_pow2 x k) by lia;
        let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v
  | |- context [Z.shiftl ?x ?k] => is_Zlit k; rewrite (Z.shiftl_mul_pow2 x k) by lia;
        let v := eval vm_compute in (2 ^ k)%Z in change (2 ^ k)%Z with v
  end.

Ltac at_stop stops :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) =>
      let b := eval vm_compute in (existsb (Z.eqb q) stops) in
      lazymatch b with true => idtac end
  end.
Ltac clear_shl := repeat match goal with H : ov_read_bytes _ _ _ 1 = Some [_] |- _ => clear H end.

(* [comment removed for export] *)
Ltac frame_step :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | OpImm ALU_ADD ?rd ?rs ?imm =>
        let d := eval vm_compute in (bv_unsigned rd) in
        let r := eval vm_compute in (bv_unsigned rs) in
        lazymatch d with 2%Z => lazymatch r with 2%Z =>
          let k := eval vm_compute in (bv_signed imm) in
          lazymatch k with
          | Zneg _ =>
              let n := eval vm_compute in (Z.to_nat (- k)) in
              reg_val rs ltac:(fun v =>
                lazymatch v with
                | Z_to_bv 64 ?E =>
                    lazymatch goal with
                    | ST : stk _ _ _ E |- _ => carve_frame n ST; lstep
                    end
                end)
          | Zpos _ =>
              reg_val rs ltac:(fun v =>
                lazymatch v with
                | Z_to_bv 64 ?E =>
                    lazymatch goal with
                    | ST : stk _ _ _ E, FRx : rw_cells _ _ E _ |- _ =>
                        lazymatch E with
                        | (?b + ?c)%Z =>
                            let v := eval vm_compute in (c + k)%Z in
                            lazymatch v with
                            | 0%Z => lstep; release_frame FRx ST b
                            | _ => lstep; release_frame FRx ST (b + v)%Z
                            end
                        end
                    end
                end)
          end end end
    end).

(* [comment removed for export] *)
Ltac special_step := fail.

(* [comment removed for export] *)
Ltac awalk1 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
(* [comment removed for export] *)
Ltac awalk stops := repeat (tryif at_stop stops then fail else awalk1).
Ltac awalk0 := awalk (@nil Z).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac merge3 PC r1 r2 r3 :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?m ?ro) =>
      eapply (evt_cut segs (fun ms' => exists u1 u2 u3 : word,
                 ms' = MS (@bvmap_set 5 word r1 u1 (@bvmap_set 5 word r2 u2 (@bvmap_set 5 word r3 u3 R))) F (Z_to_bv 64 PC) fc rv m ro));
      [ | let u1 := fresh "u" in let u2 := fresh "u" in let u3 := fresh "u" in let E := fresh "E" in
          let ms := fresh "ms" in intros ms (u1 & u2 & u3 & E); subst ms; norm_regset ]
  end.
Ltac merge_done := apply evt_done; do 3 eexists; norm_regset; reflexivity.
