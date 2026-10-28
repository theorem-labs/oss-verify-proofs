(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import SFModel Arr SysStep Image FP ITree Nodes Decode.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Bytes PropExec.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import Printf_lib F_memset F_memcpy F_fwritex F_pop_arg F_printf_iface F_printf_core.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgU Require Import F_printf_snsink F_sn_write F_towrite.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Definition zpk__ (P : Prop) : Prop := P.
Local Ltac zpk1__ H := let T := type of H in change (zpk__ T) in H.
Local Ltac zpk_nf__ H A q := lazymatch A with context [q] => fail | _ => zpk1__ H end.

Local Ltac zidleF__ q n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(q, q + n)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : ro_cells segs m ?A _ |- _ => zpk_nf__ H A q
    | H : u8arr segs m ?A _ |- _ => zpk_nf__ H A q
    | H : bytes_at segs m ?A _ |- _ => zpk_nf__ H A q
    end
  end.
Module DJ.
  Import Ltac2.
  Ltac2 prune_reld () : unit :=
    let bad := SF2.bad_heads () in
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => if SF2.plain_arith false ty then SF2.clean bad ty else SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_reld1 () : unit := Control.enter prune_reld.
End DJ.
Local Ltac dj_prune := ltac2:(DJ.prune_reld1 ()).

Module DJR.
  Import Ltac2.
  Ltac2 is_hidden (t : constr) : constr option := lazy_match! t with sf_hide ?p => Some p | _ => None end.
  Ltac2 unhide_rel () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    let rm := List.map_filter (fun h => let (id, body, ty) := h in
      match body with
      | Some _ => None
      | None =>
          match is_hidden ty with
          | Some p => if SF2.meets (SF2.vars_of [] p) gv
                      then (let c := Control.hyp id in ltac1:(c |- unfold sf_hide in c) (Ltac1.of_constr c); None)
                      else Some id
          | None => None
          end
      end) (Control.hyps ()) in
    match rm with [] => () | _ :: _ => Std.clear rm end.
  Ltac2 unhide_rel1 () : unit := Control.enter unhide_rel.
End DJR.
Local Ltac dj_unhide_rel := ltac2:(DJR.unhide_rel1 ()).
Local Ltac dj_one := first [ Zify.zify; xlia zchecker | dj_unhide_rel; Zify.zify; xlia zchecker | sf_unhide; dj_prune; Zify.zify; xlia zchecker | tlia ].
Local Ltac tslia ::= first [ exact I | repeat lazymatch goal with |- _ /\ _ => split end; first [ exact I | dj_one ] ].
Local Ltac lia ::= lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Lemma arg_ok_vf : forall Fp B BS m m' lo sp sp' ap w a,
  arg_ok Fp B BS m lo sp ap w a -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> arg_ok Fp B BS m' lo sp' ap w a.
Proof.
  intros Fp B BS m m' lo sp sp' ap w a H Hsp MU. destruct a as [s| |i|u|u|d]; cbn in H |- *; try exact H.
  destruct H as (slack & BY & HF & PAD & NZ & D1 & D2 & D3 & D4). exists slack.
  split; [|repeat (split; [first [assumption | lia]|]); exact D4].
  eapply bytes_at_transport; [exact BY | exact MU |].
  cbn [disjoint_from]. rewrite length_app, zb_length. cbn [length]. unfold zlength in *. lia.
Qed.
Lemma args_ok_vf : forall Fp B BS m m' lo sp sp' ap ws args,
  args_ok Fp B BS m lo sp ap ws args -> sp' <= sp -> munch [(lo, sp); (Fp, Fp + 232)] m m' -> args_ok Fp B BS m' lo sp' ap ws args.
Proof.
  intros Fp B BS m m' lo sp sp' ap ws args. revert ws. induction args as [|a args IH]; intros ws H Hsp MU; [destruct ws; exact I|].
  cbn [args_ok] in H |- *. destruct ws as [|w ws]; [exact H|]. destruct H as [H1 H2].
  split; [eapply arg_ok_vf; eassumption | apply IH; assumption].
Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells bgusegs m A cs -> A = A' -> rw_cells bgusegs m A' cs.
Proof. intros m A A' cs H <-. exact H. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
  gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase 0x2ba0c0 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Definition snfile_rest (CK : Z) : list cell :=
  [C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].

Definition VF_FRAME : Z := 368.

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom bgusegs)
    /\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono bgusegs m m' /\ mem_inv bgusegs m'
    /\ frm0 fc'
    /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk bgusegs m' lo (bv_unsigned sp)
    /\ ssp_cells m' canary
    /\ rw_cells bgusegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
    /\ rw_cells bgusegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
    /\ rw_cells bgusegs m' Fp [CB 232 fjunk].

Definition vfprintf_sn_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
         (lo : Z) (canary : word) (r : Z) (o : list Z),
    let q := bv_unsigned sp in
    a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
    rw_cells bgusegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells bgusegs m (Fp + 148) (snfile_rest CK) ->
    rw_cells bgusegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
    rw_cells bgusegs m D [CB dn junkd] ->
    bytes_at bgusegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
    va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
    printf_model OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (r, o)) ->
    fp_calls (length fmt) fmt args = [] ->
    (length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
    stk bgusegs m lo q -> (lo <= q - VF_FRAME - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
    ssp_cells m canary -> mem_inv bgusegs m -> frm0 fc ->
    (65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
    (q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
    (q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
    (D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D) ->
    evt bgusegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b563c) fc None m (seg_rom bgusegs)).

