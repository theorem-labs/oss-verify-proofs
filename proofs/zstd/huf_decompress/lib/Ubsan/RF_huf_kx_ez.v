(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr.
Import ListNotations. Import KXS.
Open Scope Z_scope.

Lemma kxz_ez_add : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_ADD a b) = ta + tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma kxz_ez_sub : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EAlu ALU_SUB a b) = ta - tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma kxz_ez_mul : forall zv E a b ta tb, ez zv E a = ta -> ez zv E b = tb -> ez zv E (EMd M_MUL a b) = ta * tb.
Proof. intros zv E a b ta tb <- <-. reflexivity. Qed.
Lemma kxz_ez_srl : forall zv E a sh ta, ez zv E a = ta -> ez zv E (EAlu ALU_SRL a (ELit sh)) = (ta mod 2^64) / 2^(sh mod 64).
Proof. intros zv E a sh ta <-. reflexivity. Qed.
Lemma kxz_ez_lit : forall zv E z, ez zv E (ELit z) = z.
Proof. reflexivity. Qed.
Lemma kxz_ez_hi : forall zv E j, Nat.ltb j (length zv) = false -> ez zv E (EVar j) = bv_unsigned (ev E j).
Proof. intros zv E j H. cbn [ez]. rewrite H. reflexivity. Qed.
Lemma kxz_ez_lo : forall zv E j x, Nat.ltb j (length zv) = true -> nth j zv 0 = x -> ez zv E (EVar j) = x.
Proof. intros zv E j x H <-. cbn [ez]. rewrite H. reflexivity. Qed.

Ltac kxz_ez_pf zv E e :=
  lazymatch e with
  | EAlu ALU_ADD ?a ?b => let pa := kxz_ez_pf zv E a in let pb := kxz_ez_pf zv E b in constr:(kxz_ez_add zv E a b _ _ pa pb)
  | EAlu ALU_SUB ?a ?b => let pa := kxz_ez_pf zv E a in let pb := kxz_ez_pf zv E b in constr:(kxz_ez_sub zv E a b _ _ pa pb)
  | EMd M_MUL ?a ?b => let pa := kxz_ez_pf zv E a in let pb := kxz_ez_pf zv E b in constr:(kxz_ez_mul zv E a b _ _ pa pb)
  | EAlu ALU_SRL ?a (ELit ?sh) => let pa := kxz_ez_pf zv E a in constr:(kxz_ez_srl zv E a sh _ pa)
  | ELit ?z => constr:(kxz_ez_lit zv E z)
  | EVar ?j =>
      lazymatch eval vm_compute in (Nat.ltb j (length zv)) with
      | false => constr:(kxz_ez_hi zv E j eq_refl)
      | true => let x := eval cbv [nth] in (nth j zv 0) in constr:(kxz_ez_lo zv E j x eq_refl eq_refl)
      end
  | _ => constr:(@eq_refl Z (bv_unsigned (edenot E e)) : ez zv E e = bv_unsigned (edenot E e))
  end.

Ltac kxz_cell_value Hn zv E xs v :=
  rewrite (ez_ok zv E (kE_atoms zv xs) v) in Hn;
  let EQ := fresh "HCe" in let pf := kxz_ez_pf zv E v in pose proof pf as EQ; rewrite EQ in Hn; clear EQ;
  rewrite ?Z_to_bv_bv_unsigned in Hn.

Ltac kxz_cell_gen H W :=
  lazymatch goal with
  | HLF : log_flat ?E ?log |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
    let b := eval unfold E in E in
    lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
      lazymatch type of H with
      | rw_cells ?segs m ?A [?c0] =>
          let rec go pre l :=
            lazymatch l with
            | SE ?a W ?v :: ?rest =>
                first [ let Hn := fresh "HC" in
                        assert (Hn : rw_cells segs (mem_denot E m (pre ++ SE a W v :: rest)) A
                                       [ltac:(lazymatch W with 8%nat => exact (C8 (edenot E v)) | _ => exact (C4 (edenot E v)) end)])
                          by (first [ eapply (kx_cell_store8 segs E m pre a v rest A)
                                    | eapply (kx_cell_store4 segs E m pre a v rest A) ];
                              [ change (pre ++ SE a W v :: rest) with log; exact HLF
                              | exact H
                              | change E with (kE zv xs); kx_estart_z zv
                              | change E with (kE zv xs); apply log_apart_ez_ok; kx_log_z zv ]);
                        change (pre ++ SE a W v :: rest) with log in Hn;
                        kxz_cell_value Hn zv E xs v;
                        clear H; rename Hn into H
                      | let pre' := eval cbn [app] in (pre ++ [SE a W v]) in go pre' rest ]
            | ?e :: ?rest => let pre' := eval cbn [app] in (pre ++ [e]) in go pre' rest
            | [] => fail "kxz_cell: no store to" A
            end in
          let l := eval hnf in log in
          go constr:(@nil sentry) l
      end
    end
  end.
Ltac kxz_cell H := kxz_cell_gen H 8%nat.
Ltac kxz_cell4 H := kxz_cell_gen H 4%nat.

Ltac kxz_cells_post :=
  repeat match goal with
  | HLF : log_flat ?E ?log, H : rw_cells ?segs ?m ?A [?c] |- context [MS _ _ _ _ _ (mem_denot ?E ?m ?log) _] =>
      let l := eval hnf in log in
      lazymatch A with
      | _ + ?off => tryif kx_log_has_off l off then first [ kxz_cell H | kxz_cell4 H | kx_frame H ] else kx_frame H
      | _ => first [ kxz_cell H | kxz_cell4 H | kx_frame H ]
      end
  end;
  try (cbn [cells_size csize]; lia).
