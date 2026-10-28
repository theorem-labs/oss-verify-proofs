From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_y4s31_kit.
Import ListNotations.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma xk_shl1 : forall v, v ≪ 1 = 2 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Lemma xk_zx32 : forall x, 0 <= x < 2^32 -> zx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma xk_land7 : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma xk_swrap32 : forall x, -2^31 <= x < 2^31 -> bv_swrap 32 x = x.
Proof. intros x H. apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia. Qed.

Ltac xk_bnorm_goal tl :=
  repeat (match goal with |- context [Z.land ?x 7] => rewrite (xk_land7 x) end);
  repeat (match goal with |- context [Z.shiftl ?x 3] =>
            replace (Z.shiftl x 3) with (x * 8) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity) end);
  repeat (match goal with |- context [(?a * ?k) mod 18446744073709551616] =>
            is_Zlit k; rewrite (Z.mod_small (a * k) 18446744073709551616) by llia end);
  repeat (match goal with |- context [(?a * ?k) mod 4294967296] =>
            is_Zlit k; rewrite (Z.mod_small (a * k) 4294967296) by llia end);
  repeat (match goal with |- context [bv_swrap 32 ?x] =>
            lazymatch x with context [tl] => fail | _ => rewrite (xk_swrap32 x) by llia end end);
  repeat (match goal with |- context [zx32 (Z_to_bv 64 ?x)] =>
            lazymatch x with context [tl] => fail | _ => rewrite (xk_zx32 x) by llia end end).

Ltac xk_bnorm_in H tl := revert H; xk_bnorm_goal tl; intro H.

Ltac xk_cell tl cells TCK :=
  match goal with VR : 0 <= ?v < 2^tl |- _ =>
    lazymatch goal with
    | _ : _ = nth (Z.to_nat v) cells x1_default |- _ => fail
    | |- _ =>
      let c := fresh "c" in let EC := fresh "EC" in
      remember (nth (Z.to_nat v) cells x1_default) as c eqn:EC;
      let NB := fresh "NB" in let BY := fresh "BY" in
      destruct (TCK v VR) as (NB & BY); rewrite <- EC in NB, BY end end.

Ltac xk_rd_clear DT :=
  repeat match goal with H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 2 * _ + _)) _ = _ |- _ => clear H
                     | H : ov_read_bytes usegs _ (Z_to_bv 64 (DT + 4 + 2 * _)) _ = _ |- _ => clear H end.

Ltac xk_rd tl DT cells cbs ECB :=
  xk_rd_clear DT;
  lazymatch goal with EC : ?c = nth (Z.to_nat ?v) cells x1_default, CE : bytes_at usegs ?mm (DT + 4) cbs |- _ =>
    let R0 := fresh "RC" in let R1 := fresh "RC" in
    destruct (x1_cell_rd usegs mm (DT + 4) cells (Z.to_nat (2 * 2^tl)) v ltac:(rewrite <- ECB; exact CE)
                ltac:(lia) ltac:(lia) ltac:(lia)) as [R0 R1];
    rewrite <- EC in R0, R1 end.

Ltac xk_gen :=
  repeat (match goal with |- context [Z.lor ?a ?b] =>
            let cw := fresh "cw" in set (cw := Z.lor a b) in *; clearbody cw end).

Ltac xk_norm tl :=
  xk_gen;
  try (let v := fresh "v" in uidx tl v);
  try rewrite xk_shl1;
  xk_bnorm_goal tl;
  try (rewrite ?u_srl3 by lia);
  try (rewrite u_shamt by lia);
  repeat (match goal with |- context [(?a / 8) mod 18446744073709551616] => rewrite (Z.mod_small (a / 8) 18446744073709551616) by llia end);
  repeat (match goal with |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (sx32_small z) by lia end);
  repeat (match goal with
          | |- context [bv_unsigned (Z_to_bv 8 (x1_nbBits ?c))] => rewrite (byte_lit (x1_nbBits c)) by lia
          | |- context [bv_unsigned (Z_to_bv 8 (x1_byte ?c))] => rewrite (byte_lit (x1_byte c)) by lia end).

Ltac xk_kind :=
  lazymatch goal with |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
        let d := eval vm_compute in (decode_any w) in
        lazymatch d with
        | Some (Load _ _ _ _ _, _) => constr:(1)
        | Some (Store _ _ _ _, _) => constr:(2)
        | _ => constr:(0)
        end
    | _ => constr:(0)
    end end.

Ltac xk_step tl DT cells cbs ECB OUT LB SRC :=
  let kd := xk_kind in
  lazymatch kd with
  | 0 => zstep
  | _ =>
      lazymatch type of OUT with u8arr _ _ ?A _ =>
        let E := u_mem_addr in
        lazymatch E with
        | bv_unsigned _ + _ + _ => zstep
        | bv_unsigned _ + _ => zstep
        | context [DT] => xk_rd tl DT cells cbs ECB; zstep
        | context [A] => ustore OUT LB
        | _ => usrc SRC; zstep
        end end
  end.

Ltac xwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC :=
  lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        lazymatch eval vm_compute in (orb (existsb (Z.eqb pc) stops) (u_is_chk usegs pc)) with
        | true => fail
        | false =>
            xk_norm tl;
            repeat (xk_cell tl cells TCK);
            first [ xk_step tl DT cells cbs ECB OUT LB SRC | zstep | ustore OUT LB | xk_rd tl DT cells cbs ECB; zstep | usrc SRC; zstep ]
        end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let H := fresh "B" in
        if_cases H; zify_cond H; hnorm H;
        first [ solve [zlean H]
              | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                  lazymatch eval vm_compute in (u_is_chk usegs pc) with
                  | true => solve [unorm H; zrefute H]
                  end end
              | idtac ]
    end.

Ltac xwalk stops tl DT cells cbs ECB TCK OUT LB SRC := repeat (xwalk1 stops tl DT cells cbs ECB TCK OUT LB SRC).
