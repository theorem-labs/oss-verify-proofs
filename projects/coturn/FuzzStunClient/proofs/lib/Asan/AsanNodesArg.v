(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module AN.
Import AX2. Import APC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record argtab : Type := ARGT {
  g_istrlen : Z;        (* [comment removed for export] *)
  g_memchr : Z;         (* [comment removed for export] *)
  g_stdio_write : Z;    (* [comment removed for export] *)
  g_exit : Z;           (* [comment removed for export] *)
  g_file_lo : Z; g_file_hi : Z;     (* [comment removed for export] *)
  g_canary_got : Z; g_canary : Z;   (* [comment removed for export] *)
  g_ro_lo : Z; g_ro_hi : Z          (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition ARG_ASAN : argtab :=   (* [comment removed for export] *)
  {| g_istrlen := 0x66310; g_memchr := 0xa40b0; g_stdio_write := 0x9fea4; g_exit := 0x9a904;
     g_file_lo := 0xaf468; g_file_hi := 0xaf730; g_canary_got := 0xabb08; g_canary := 0x606630;
     g_ro_lo := 0x10360; g_ro_hi := 0x10388 |}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARG_BOTH : argtab :=
  {| g_istrlen := 0x66300; g_memchr := 0xa26ec; g_stdio_write := 0x9e4e0; g_exit := 0x98f40;
     g_file_lo := 0xadaa8; g_file_hi := 0xadd70; g_canary_got := 0xaa140; g_canary := 0x604bf0;
     g_ro_lo := 0x10360; g_ro_hi := 0x10388 |}.
Definition argtab_of (A : atable) : argtab :=
  if Z.eqb (img_hi A) 0x608000 then ARG_ASAN else ARG_BOTH.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LMAX : Z := 131071.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition TOPNUL : Z := 2 ^ 47 - 17.
Definition STRLO : Z := 0x7fff80000000 + 176.   (* [comment removed for export] *)

Definition arg_idx (args : list expr) : option nat :=
  match args with
  | [ELit 0] => Some 0%nat
  | [ELit 1] => Some 1%nat
  | _ => None
  end.
Definition str_e (i : nat) : expr := match i with O => e_str0 | _ => e_str1 end.
Definition len_e (i : nat) : expr := match i with O => EVar V_L0 | _ => EVar V_L1 end.
Definition blob_of (i : nat) : nat := match i with O => 1%nat | _ => 2%nat end.
(* [comment removed for export] *)
Definition nul_e (i : nat) : expr := eadd (str_e i) (len_e i).

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : N.
Let G : argtab := argtab_of A.

(* [comment removed for export] *)
Definition eeq (k : list kentry) (a b : expr) : bool :=
  expr_eqb a b || (lin_ge0 k [(a, 0)] [(b, 0)] && lin_ge0 k [(b, 0)] [(a, 0)]).

(* [comment removed for export] *)
Definition argc_ok (k : list kentry) (i : nat) : bool :=
  match i with
  | O => true
  | _ => match xlo k (EVar V_ARGC) with Some lo => Z.leb 2 lo | None => false end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition str_hi (k : list kentry) (i : nat) : Z :=
  match xlo k (len_e i) with Some lo => TOPNUL - Z.max 0 lo | None => TOPNUL end.
Definition ioff (i : nat) : Z := match i with O => 0 | _ => 1 end.
Definition str_facts (k : list kentry) (i : nat) : list kentry :=
  [KRange (str_e i) (STRLO + ioff i) (str_hi k i); KRange (nul_e i) (STRLO + ioff i) TOPNUL].
(* [comment removed for export] *)
Definition srl_facts (k : list kentry) (i : nat) : list kentry :=
  [KRange (mkSrl k (str_e i) 3) (STRLO / 8) (str_hi k i / 8); KRange (mkSrl k (nul_e i) 3) (STRLO / 8) (TOPNUL / 8)].
(* [comment removed for export] *)
Definition len_fact (k : list kentry) (i : nat) : list kentry :=
  match xhi k (len_e i) with
  | Some hi => if Z.leb hi LMAX then [] else [KRange (len_e i) 0 LMAX]
  | None => [KRange (len_e i) 0 LMAX]
  end.
(* [comment removed for export] *)
Definition strlen_facts1 (k : list kentry) (i : nat) : list kentry :=
  len_fact k i ++ match i with O => [] | _ => str_facts k 1 end ++ str_facts k 0.
Definition strlen_facts2 (k : list kentry) (i : nat) : list kentry :=
  match i with O => [] | _ => srl_facts k 1 end ++ srl_facts k 0.

(* [comment removed for export] *)
Definition kimg_cover (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_argstrlen (cs : acs) (args : list expr) : option acs :=
  match arg_idx args, ret_lit cs with
  | Some i, Some ret =>
      if (Z.eqb (pc cs) (g_istrlen G) && eeq (kn cs) (reg cs 10) (str_e i) && argc_ok (kn cs) i)%bool
      then let cs1 := add_kn cs (strlen_facts1 (kn cs) i) in
           let cs2 := add_kn cs1 (strlen_facts2 (kn cs1) i) in
           Some (set_pc (set_reg (set_reg (set_reg cs2 10 (len_e i)) 11 (eaddz (len_e i) 1)) 12 (ELit 0)) ret)
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_argmemchr (cs : acs) (args : list expr) : option acs :=
  match arg_idx args, ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some i, Some ret, Some c, Some n =>
      if (Z.eqb (pc cs) (g_memchr G) && eeq (kn cs) (reg cs 10) (str_e i) && Z.eqb c 0
          && Z.leb (LMAX + 8) n && Z.ltb n (2 ^ 63) && argc_ok (kn cs) i
          && kimg_cover (kn cs) (g_ro_lo G) (g_ro_hi G))%bool
      then after_call nx0 cs ret (Some (nul_e i)) (kn cs)
      else None
  | _, _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_argnul (cs : acs) (args : list expr) : option acs :=
  match arg_idx args with
  | Some i =>
      if (Z.leb 0 (pc cs) && Z.ltb (pc cs + 4) two64 && argc_ok (kn cs) i)%bool then
        match fetch_word segs (Z_to_bv 64 (pc cs)) with
        | Some w =>
            if is_ecall w then None else
            match decode_any w with
            | Some (Load SZ1 false rd rs imm, 4) =>
                if (negb (bv_eqb rd 0%bv) && negb (bv_eqb rs 0%bv)
                    && eeq (kn cs) (eaddz (reg cs (ridx rs)) (bv_signed imm)) (nul_e i))%bool
                then Some (set_pc (set_reg cs (ridx rd) (ELit 0)) (pc cs + 4))
                else None
            | _ => None
            end
        | None => None
        end
      else None
  | None => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_memcpyarg (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  match arg_idx args, ret_lit cs with
  | Some i, Some ret =>
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      let ne := len_e i in
      if (Z.eqb (pc cs) (x_memcpy A) && eeq k (reg cs 11) (str_e i) && eeq k (reg cs 12) ne
          && argc_ok k i)%bool
      then match base_range k db, xlo k ne, xhi k ne with
           | Some (dlo, dhi), Some nlo, Some nhi =>
               if (Z.leb 0 nlo && Z.leb nhi LMAX && Z.leb 0 (dlo + dk) && Z.ltb (dhi + dk + LMAX) two64
                   && off_image_x A k db dk ne && kwritable_x k k db dk ne
                   && lin_ge0 k [(e_sp0, 0)] [(dst, 0); (ne, 0)])%bool
               then after_call nx0 cs ret (Some dst) (KBlob (SA db dk) ne (blob_of i) :: kn_havoc k db dk ne)
               else None
           | _, _, _ => None
           end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_blob (k : list kentry) (cb : expr) (ck : Z) : option (expr * nat) :=
  match k with
  | [] => None
  | KBlob (SA b o) n bk :: rest => if (expr_eqb b cb && Z.eqb o ck)%bool then Some (n, bk) else find_blob rest cb ck
  | _ :: rest => find_blob rest cb ck
  end.

Definition flush_lit (lit : list Z) (acc : list spiece) : list spiece :=
  match lit with [] => acc | _ => SPLit (rev lit) :: acc end.

(* [comment removed for export] *)
Fixpoint pieces_walk (fuel : nat) (k : list kentry) (c wp : expr) (lit : list Z) (acc : list spiece)
  : option (list spiece) :=
  match fuel with
  | O => None
  | S f =>
      if eeq k c wp then Some (rev (flush_lit lit acc)) else
      let '(cb, ck) := split_lit c in
      match (match find_blob k cb ck with
             | Some (n, b) => match foldK k n with ELit 0 => None | n' => Some (n', b) end  (* [comment removed for export] *)
             | None => None
             end) with
      | Some (n', b) =>
          (* [comment removed for export] *)
          if match xhi k c, xhi k n' with Some ch, Some nh => Z.ltb (ch + nh) two64 | _, _ => false end
          then pieces_walk f k (eadd c n') wp [] (SPBlob b :: flush_lit lit acc)
          else None
      | None =>
          match kreadZ segs k cb ck 1 with
          | Some z => if flat_x k cb ck (ELit 2) then pieces_walk f k (eaddz c 1) wp (z :: lit) acc else None
          | None => None
          end
      end
  end.
Definition PIECES_FUEL : nat := 4200%nat.

(* [comment removed for export] *)
Definition extra_pieces (k : list kentry) (s l : expr) : option (list spiece) :=
  let lz := match l with ELit z => Some (z mod two64) | _ => None end in
  match lz with
  | Some 0 => Some []
  | _ =>
    if (eeq k s (str_e 0) && eeq k l (len_e 0))%bool then Some [SPBlob (blob_of 0)]
    else if (eeq k s (str_e 1) && eeq k l (len_e 1) && argc_ok k 1)%bool then Some [SPBlob (blob_of 1)]
    else let '(sb, sk) := split_lit s in
         match find_blob k sb sk with
         | Some (n, b) => if eeq k n l then Some [SPBlob b] else None
         | None =>
             match lz with
             | Some z => if flat_x k sb sk (ELit z) then
                           match kread_bytes segs (Z.to_nat z) k sb sk with
                           | Some bs => Some [SPLit bs]
                           | None => None
                           end
                         else None
             | None => None
             end
         end
  end.

(* [comment removed for export] *)
Definition off_lazy (k : list kentry) (b : expr) (n : expr) : bool :=
  match xhi k (eadd b n), xlo k b with
  | Some hi, Some lo => (Z.leb (img_lo A) lo && Z.leb hi (img_hi A)) || (Z.leb 0 lo && lin_ge0 k [(b, 0)] [(e_top, 0)])
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition node_stdio_write_ref (cs : acs) : option (Z * list spiece * acs) :=
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
      match pieces_walk PIECES_FUEL k WB WP [] [], extra_pieces k s l,
            xlo k sp, xhi k sp, xhi k np, xhi k l, xhi k s, xlo k WB, xhi k WP with
      | Some pend, Some extra, Some splo, Some sphi, Some nphi, Some lhi, Some shi, Some wblo, Some wphi =>
        if (((fd =? 1) || (fd =? 2)) && (cg =? g_canary G)
            && (0 <=? wblo) && (wphi <=? 2 ^ 47)   (* [comment removed for export] *)
            && (nphi + lhi <=? 2 ^ 30)   (* [comment removed for export] *)
            && kwritable k k qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? 2 ^ 47)
            && ((shi + lhi <=? 2 ^ 47) || lin_ge0 k [(ELit (2 ^ 47), 0)] [(s, 0); (l, 0)])   (* [comment removed for export] *)
            && lin_ge0 k [(WP, 0)] [(WB, 0)]
            && (lin_ge0 k [(spm, 0)] [(WP, 0)] || lin_ge0 k [(WB, 0)] [(sp, 0)])
            && (lin_ge0 k [(spm, 0)] [(s, 0); (l, 0)] || lin_ge0 k [(s, 0)] [(sp, 0)])
            && (CEIL + 112 <=? splo) && lin_ge0 k [(sp, -112)] [(e_top, 0)] && off_lazy k WB np   (* [comment removed for export] *) && (match l with ELit 0 => true | _ => off_lazy k s l end)
            && expr_vars_lt (nxt cs) bufp && expr_vars_lt (nxt cs) bufsz)%bool
        then
          let k0 := kimg_cut (kimg_cut k (f + 32) 16) (f + 56) 8 in
          let k1 := kn_havoc k0 qb qk (ELit 112) in
          let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16) in
          let k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8) in
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition eeqB (bc : AX2B.bctx) (a b : expr) : bool :=
  if expr_eqb a b then true else if AX2B.lin_ge0B bc [(a, 0)] [(b, 0)] then AX2B.lin_ge0B bc [(b, 0)] [(a, 0)] else false.
Lemma eeqB_eqf : forall k, eeqB (AX2B.mkbc k) = eeq k.
Proof.
  intros k. apply functional_extensionality; intros a. apply functional_extensionality; intros b.
  unfold eeqB, eeq. rewrite AX2B.lin_ge0B_eqf. reflexivity.
Qed.

Definition argc_okB (bc : AX2B.bctx) (i : nat) : bool :=
  match i with
  | O => true
  | _ => match AX2B.xloB bc (EVar V_ARGC) with Some lo => Z.leb 2 lo | None => false end
  end.
Lemma argc_okB_eqf : forall k, argc_okB (AX2B.mkbc k) = argc_ok k.
Proof. intros k. apply functional_extensionality; intros i. unfold argc_okB, argc_ok. rewrite AX2B.xloB_eqf. reflexivity. Qed.

Fixpoint pieces_walkB (bc : AX2B.bctx) (kx : AX2B.kix) (k : list kentry) (fuel : nat) (c wp : expr) (lit : list Z) (acc : list spiece) {struct fuel}
  : option (list spiece) :=
  match fuel with
  | O => None
  | S f =>
      if eeqB bc c wp then Some (rev (flush_lit lit acc)) else
      let '(cb, ck) := split_lit c in
      match (match find_blob k cb ck with
             | Some (n, b) => match AX2B.foldKB bc n with ELit 0 => None | n' => Some (n', b) end
             | None => None
             end) with
      | Some (n', b) =>
          if match AX2B.xhiB bc c, AX2B.xhiB bc n' with Some ch, Some nh => Z.ltb (ch + nh) two64 | _, _ => false end
          then pieces_walkB bc kx k f (eadd c n') wp [] (SPBlob b :: flush_lit lit acc)
          else None
      | None =>
          match kreadZBX segs bc kx cb ck 1 with
          | Some z => if flat_xB bc cb ck (ELit 2) then pieces_walkB bc kx k f (eaddz c 1) wp (z :: lit) acc else None
          | None => None
          end
      end
  end.
Lemma pieces_walkB_eq : forall k fuel c wp lit acc, pieces_walkB (AX2B.mkbc k) (AX2B.mk_kix k) k fuel c wp lit acc = pieces_walk fuel k c wp lit acc.
Proof.
  intros k fuel. induction fuel as [|f IH]; intros c wp lit acc; [reflexivity|].
  cbn [pieces_walkB pieces_walk]. rewrite eeqB_eqf. destruct (eeq k c wp); [reflexivity|].
  destruct (split_lit c) as [cb ck].
  rewrite AX2B.foldKB_eqf, AX2B.xhiB_eqf, kreadZBX_eqf, flat_xB_eqf.
  destruct (match find_blob k cb ck with
            | Some (n, b) => match foldK k n with ELit 0 => None | n' => Some (n', b) end
            | None => None
            end) as [[n' b]|].
  - destruct (match xhi k c, xhi k n' with Some ch, Some nh => Z.ltb (ch + nh) two64 | _, _ => false end); [apply IH|reflexivity].
  - destruct (kreadZ segs k cb ck 1) as [z|]; [|reflexivity]. destruct (flat_x k cb ck (ELit 2)); [apply IH|reflexivity].
Qed.
Lemma pieces_walkB_eqf : forall k, pieces_walkB (AX2B.mkbc k) (AX2B.mk_kix k) k = fun fuel => pieces_walk fuel k.
Proof.
  intros k. apply functional_extensionality; intros fuel. apply functional_extensionality; intros c.
  apply functional_extensionality; intros wp. apply functional_extensionality; intros lit.
  apply functional_extensionality; intros acc. apply pieces_walkB_eq.
Qed.

Definition extra_piecesB (bc : AX2B.bctx) (kx : AX2B.kix) (k : list kentry) (s l : expr) : option (list spiece) :=
  let lz := match l with ELit z => Some (z mod two64) | _ => None end in
  match lz with
  | Some 0 => Some []
  | _ =>
    if (if eeqB bc s (str_e 0) then eeqB bc l (len_e 0) else false) then Some [SPBlob (blob_of 0)]
    else if (if (if eeqB bc s (str_e 1) then eeqB bc l (len_e 1) else false) then argc_okB bc 1 else false) then Some [SPBlob (blob_of 1)]
    else let '(sb, sk) := split_lit s in
         match find_blob k sb sk with
         | Some (n, b) => if eeqB bc n l then Some [SPBlob b] else None
         | None =>
             match lz with
             | Some z => if flat_xB bc sb sk (ELit z) then
                           match kread_bytesBX segs bc kx (Z.to_nat z) sb sk with
                           | Some bs => Some [SPLit bs]
                           | None => None
                           end
                         else None
             | None => None
             end
         end
  end.
Lemma extra_piecesB_eqf : forall k, extra_piecesB (AX2B.mkbc k) (AX2B.mk_kix k) k = extra_pieces k.
Proof.
  intros k. apply functional_extensionality; intros s. apply functional_extensionality; intros l.
  unfold extra_piecesB, extra_pieces. rewrite eeqB_eqf, argc_okB_eqf, flat_xB_eqf, kread_bytesBX_eqf. reflexivity.
Qed.

Definition off_lazyB (bc : AX2B.bctx) (b : expr) (n : expr) : bool :=
  match AX2B.xhiB bc (eadd b n), AX2B.xloB bc b with
  | Some hi, Some lo => if (Z.leb (img_lo A) lo && Z.leb hi (img_hi A))%bool then true
                        else if Z.leb 0 lo then AX2B.lin_ge0B bc [(b, 0)] [(e_top, 0)] else false
  | _, _ => false
  end.
Lemma off_lazyB_eqf : forall k, off_lazyB (AX2B.mkbc k) = off_lazy k.
Proof.
  intros k. apply functional_extensionality; intros b. apply functional_extensionality; intros n.
  unfold off_lazyB, off_lazy. rewrite AX2B.xhiB_eqf, AX2B.xloB_eqf, AX2B.lin_ge0B_eqf. reflexivity.
Qed.

Definition node_stdio_write (cs : acs) : option (Z * list spiece * acs) :=
  let k := kn cs in
  match ret_lit cs, reg_lit cs 10 with
  | Some ret, Some f =>
    if negb (Z.eqb (pc cs) (g_stdio_write G) && Z.leb (g_file_lo G) f && Z.leb (f + 232) (g_file_hi G))%bool then None else
    let bc := AX2B.mkbc k in let kx := AX2B.mk_kix k in
    match kreadZBX segs bc kx (ELit 0) (f + 120) 4, kread8eBX segs bc kx (ELit 0) (f + 40), kread8eBX segs bc kx (ELit 0) (f + 56),
          kread8eBX segs bc kx (ELit 0) (f + 88), kread8eBX segs bc kx (ELit 0) (f + 96),
          kreadZBX segs bc kx (ELit 0) (g_canary_got G) 8, kread8eBX segs bc kx (ELit 0) (g_canary G) with
    | Some fd, Some WP, Some WB, Some bufp, Some bufsz, Some cg, Some _ =>
      let s := reg cs 11 in let l := reg cs 12 in let sp := reg cs 2 in
      let spm := eaddz sp (-112) in
      let '(qb, qk) := split_lit spm in
      let np := esub WP WB in
      match pieces_walkB bc kx k PIECES_FUEL WB WP [] [], extra_piecesB bc kx k s l,
            AX2B.xloB bc sp, AX2B.xhiB bc sp, AX2B.xhiB bc np, AX2B.xhiB bc l, AX2B.xhiB bc s, AX2B.xloB bc WB, AX2B.xhiB bc WP with
      | Some pend, Some extra, Some splo, Some sphi, Some nphi, Some lhi, Some shi, Some wblo, Some wphi =>
        if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if (if Z.eqb fd 1 then true else Z.eqb fd 2)
              then Z.eqb cg (g_canary G) else false)
              then Z.leb 0 wblo else false)
              then Z.leb wphi (2 ^ 47) else false)
              then Z.leb (nphi + lhi) (2 ^ 30) else false)
              then kwritableB bc k qb qk 112 else false)
              then Z.leb (4294967296 + 112) splo else false)
              then Z.leb sphi (2 ^ 47) else false)
              then (if Z.leb (shi + lhi) (2 ^ 47) then true else AX2B.lin_ge0B bc [(ELit (2 ^ 47), 0)] [(s, 0); (l, 0)]) else false)
              then AX2B.lin_ge0B bc [(WP, 0)] [(WB, 0)] else false)
              then (if AX2B.lin_ge0B bc [(spm, 0)] [(WP, 0)] then true else AX2B.lin_ge0B bc [(WB, 0)] [(sp, 0)]) else false)
              then (if AX2B.lin_ge0B bc [(spm, 0)] [(s, 0); (l, 0)] then true else AX2B.lin_ge0B bc [(s, 0)] [(sp, 0)]) else false)
              then Z.leb (CEIL + 112) splo else false)
              then AX2B.lin_ge0B bc [(sp, -112)] [(e_top, 0)] else false)
              then off_lazyB bc WB np else false)
              then (match l with ELit 0 => true | _ => off_lazyB bc s l end) else false)
              then expr_vars_lt (nxt cs) bufp else false)
              then expr_vars_lt (nxt cs) bufsz else false)
        then
          let k0 := kimg_cut (kimg_cut k (f + 32) 16) (f + 56) 8 in
          let k1 := kn_havoc k0 qb qk (ELit 112) in
          let k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16) in
          let k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8) in
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
Lemma node_stdio_write_eq : forall cs, node_stdio_write cs = node_stdio_write_ref cs.
Proof.
  intros cs. unfold node_stdio_write, node_stdio_write_ref. cbv zeta.
  rewrite kreadZBX_eqf, kread8eBX_eqf, pieces_walkB_eqf, extra_piecesB_eqf, AX2B.xloB_eqf, AX2B.xhiB_eqf,
    kwritableB_eqf, AX2B.lin_ge0B_eqf, off_lazyB_eqf.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition two63 : Z := 2 ^ 63.
Definition node_reldiff (cs : acs) (args : list expr) : option acs :=
  match args with
  | [X; Y; ELit s] =>
      let k := kn cs in
      let '(X', wX) := deand X in let X'' := eaddz X' 0 in   (* [comment removed for export] *)
      let '(Y', wY) := deand Y in let Y'' := eaddz Y' 0 in
      if (Z.leb 0 s && Z.ltb s 64 && expr_vars_lt (nxt cs) X && expr_vars_lt (nxt cs) Y)%bool then
        match xlo1 k X'', xhi1 k X'', xlo1 k Y'', xhi1 k Y'', xlo1 k (esub Y'' X''), xhi1 k (esub Y'' X'') with
        | Some xlo', Some xhi', Some ylo', Some yhi', Some l, Some h =>
            let dlo := l - wY in
            let dhi := h + wX in
            if (Z.leb wX xlo' && Z.leb wY ylo' && Z.ltb xhi' two63 && Z.ltb yhi' two63 && Z.ltb h two63 && Z.leb 0 dlo)%bool then
              let m := 2 ^ s in
              Some (add_kn cs [KRange X (xlo' - wX) xhi'; KRange Y (ylo' - wY) yhi';
                               KRange (esub (mkSrl k Y s) (mkSrl k X s)) (dlo / m) ((dhi + m - 1) / m)])
            else None
        | _, _, _, _, _, _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zone_covers (k : list kentry) (bb : expr) (bk : Z) (N : expr) (K : kentry) : bool :=
  match K with
  | KZero (SA (ELit z) zk) (ELit zn) =>
      let lo := zlit64 z + zk in
      lin_ge0 k [(bb, bk)] [(ELit 0, lo)] && lin_ge0 k [(ELit 0, lo + zlit64 zn)] [(bb, bk); (N, 0)]
      && Z.ltb (lo + zlit64 zn) two64
  | _ => false
  end.
Definition node_zerocover (cs : acs) (args : list expr) : option acs :=
  match args with
  | [B; N] =>
      let k := kn cs in
      let '(bb, bk) := split_lit B in
      if (expr_vars_lt (nxt cs) B && expr_vars_lt (nxt cs) N && existsb (zone_covers k bb bk N) k)%bool
      then Some (add_kn cs [KZero (SA bb bk) N]) else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint take_srl (ts : list (Z * expr)) : option (Z * expr * Z * list (Z * expr)) :=
  match ts with
  | [] => None
  | (co, a) :: rest =>
      match (match a with EAlu ALU_SRL r (ELit s) => Some (r, s) | _ => None end) with
      | Some (r, s) => Some (co, r, s, rest)
      | None => match take_srl rest with
                | Some (co', r, s, rest') => Some (co', r, s, (co, a) :: rest')
                | None => None
                end
      end
  end.
(* [comment removed for export] *)
Definition node_srlbound1 (cs : acs) (e : expr) : option acs :=
      let k := kn cs in
      let l := lin_of e in
      match take_srl (snd l) with
      | Some (co, r, s, rest) =>
          if (Z.leb 0 s && Z.ltb s 64 && expr_vars_lt (nxt cs) e)%bool then
            let m := 2 ^ s in
            let e' := unlin (fst l, rest) in
            if Z.eqb co 1 then
              let J := eadd (escale m e') r in
              match xhi1 k e', xhi1 k r, xlo1 k J, xhi1 k J with
              | Some he, Some hr, Some lo, Some hi =>
                  if Z.ltb (m * he + hr) two64 then Some (add_kn cs [KRange e (lo / m) (hi / m)]) else None
              | _, _, _, _ => None
              end
            else if (Z.ltb 0 co && Z.ltb co two64 && Z.eqb (co mod m) 0)%bool then
              let q := co / m in
              let J := eadd e' (escale q r) in
              match xhi1 k e', xhi1 k r, xlo1 k J, xhi1 k J with
              | Some he, Some hr, Some lo, Some hi =>
                  if (Z.ltb (he + q * hr) two64 && Z.leb (q * (m - 1)) lo)%bool
                  then Some (add_kn cs [KRange e (lo - q * (m - 1)) hi]) else None
              | _, _, _, _ => None
              end
            else None
          else None
      | None => None
      end
.
(* [comment removed for export] *)
Definition node_srlbound (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] => match node_srlbound1 cs (reg cs (Z.to_nat r)) with Some cs' => Some cs' | None => Some cs end
  | [e] => node_srlbound1 cs e
  | _ => None
  end.

(* [comment removed for export] *)
Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 0%nat => node_argstrlen cs args
  | 1%nat => node_argmemchr cs args
  | 2%nat => node_argnul cs args
  | 3%nat => node_memcpyarg cs args
  | 5%nat => node_reldiff cs args
  | 6%nat => node_zerocover cs args
  | 7%nat => node_srlbound cs args
  | _ => None
  end.

(* [comment removed for export] *)
Definition xe (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 0%nat => node_stdio_write cs
  | _ => None
  end.

End WithSegs.
End AN.
