(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanNodesArg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFA.
Import AX2. Import APC. Import AN.

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Let G : argtab := argtab_of A.

Definition node_stdio_write_f (cs : acs) : option (Z * list spiece * acs) :=
  let k := kn cs in
  match ret_lit cs, reg_lit cs 10 with
  | Some ret, Some f =>
    if negb (Z.eqb (pc cs) (g_stdio_write G) && Z.leb (g_file_lo G) f && Z.leb (f + 232) (g_file_hi G))%bool then None else
    match kreadZ segs k (ELit 0) (f + 120) 4, kread8e segs k (ELit 0) (f + 40), kread8e segs k (ELit 0) (f + 56),
          kread8e segs k (ELit 0) (f + 88), kread8e segs k (ELit 0) (f + 96),
          kreadZ segs k (ELit 0) (g_canary_got G) 8, kread8e segs k (ELit 0) (g_canary G) with
    | Some fd, Some WP, Some WB, Some bufp, Some bufsz, Some cg, Some _ =>
      let s := reg cs 11 in let l := reg cs 12 in let sp := reg cs 2 in
      let spm := eaddz sp (-112) in
      let '(qb, qk) := split_lit spm in
      let np := esub WP WB in
      match pieces_walk segs PIECES_FUEL k WB WP [] [], extra_pieces segs k s l,
            xlo k sp, xhi k sp, xhi k np, xhi k l, xhi k s, xlo k WB, xhi k WP with
      | Some pend, Some extra, Some splo, Some sphi, Some nphi, Some lhi, Some shi, Some wblo, Some wphi =>
        if (((fd =? 1) || (fd =? 2)) && (cg =? g_canary G)
            && (0 <=? wblo) && (wphi <=? 2 ^ 47)   (* [comment removed for export] *)
            && (nphi + lhi <=? 2 ^ 26)
            && kwritable k k qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? 2 ^ 47)
            && send_ok k s l shi lhi   (* [comment removed for export] *)
            && lin_ge0 k [(WP, 0)] [(WB, 0)]
            && (lin_ge0 k [(spm, 0)] [(WP, 0)] || lin_ge0 k [(WB, 0)] [(sp, 0)])
            && (lin_ge0 k [(spm, 0)] [(s, 0); (l, 0)] || lin_ge0 k [(s, 0)] [(sp, 0)])
            && lin_ge0 k [(spm, STKMAX)] [(e_spw, 0)] && off_lazy A k WB np && (match l with ELit 0 => true | _ => off_lazy A k s l end)
            && expr_vars_lt (nxt cs) bufp && expr_vars_lt (nxt cs) bufsz)%bool
        then
          let k0 := kimg_cut (kimg_cut k (f + 32) 16) (f + 56) 8 in
          let k1 := kn_havocM k0 qb qk (ELit 112) in
          let k2 := kn_havocM k1 (ELit 0) (f + 32) (ELit 16) in
          let k3 := kn_havocM k2 (ELit 0) (f + 56) (ELit 8) in
          let k4 := KWord (SA (ELit 0) (f + 32)) 8 (eadd bufp bufsz)
                    :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                    :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3 in
          match after_call nx0 cs ret (Some l) k4 with
          | Some cs' => Some (fd, pend ++ extra, cs')
          | None => None
          end
        else None
      | _, _, _, _, _, _, _, _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

Lemma node_stdio_write_f_eq : forall cs, node_stdio_write_f cs = AN.node_stdio_write segs A nx0 cs.
Proof. intros cs. unfold node_stdio_write_f, AN.node_stdio_write. rewrite kn_havocM_eq. reflexivity. Qed.

Definition xe_f (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 0%nat => node_stdio_write_f cs
  | _ => None
  end.
Lemma xe_f_eq : forall id args cs, xe_f id args cs = AN.xe segs A nx0 id args cs.
Proof. intros id args cs. unfold xe_f, AN.xe. destruct id; [apply node_stdio_write_f_eq | reflexivity]. Qed.
End WithSegs.

End CXFA.
