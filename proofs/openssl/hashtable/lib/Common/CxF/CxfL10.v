(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AsanPlanCore.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AsanNodesArg CxfLeaf CxfNat CxfL1 CxfL2 CxfL3.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ANL.
Import AN.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import APC.
Import APCL.
Definition ARG_A0 : argtab :=
  {| g_istrlen := 0x9358c; g_memchr := 0x156064; g_stdio_write := 0x1513b4; g_exit := 0x14dd4c;
     g_file_lo := 0x162be8; g_file_hi := 0x162dc8; g_canary_got := 0x15f1a8; g_canary := 0x69ad70;
     g_ro_lo := 0x10350; g_ro_hi := 0x10370 |}.
Lemma L_ANL_ARG_A0 : @ARG_A0 = @AN.ARG_A0.
Proof. unfold ARG_A0. reflexivity. Qed.

Definition ARG_B0 : argtab :=
  {| g_istrlen := 0x92c80; g_memchr := 0x15e1e8; g_stdio_write := 0x159538; g_exit := 0x155ed0;
     g_file_lo := 0x16aea8; g_file_hi := 0x16b088; g_canary_got := 0x167328; g_canary := 0x6a3030;
     g_ro_lo := 0x10350; g_ro_hi := 0x10370 |}.
Lemma L_ANL_ARG_B0 : @ARG_B0 = @AN.ARG_B0.
Proof. unfold ARG_B0. reflexivity. Qed.

Definition ARG_H0 : argtab :=
  {| g_istrlen := 0; g_memchr := 0x276380; g_stdio_write := 0x26fa04; g_exit := 0x26bc44;
     g_file_lo := 0x2d9040; g_file_hi := 0x2d9308; g_canary_got := 0x2d7ba0; g_canary := 0x30bf98;
     g_ro_lo := 0x3a790; g_ro_hi := 0x3a7d8 |}.
Lemma L_ANL_ARG_H0 : @ARG_H0 = @AN.ARG_H0.
Proof. unfold ARG_H0. reflexivity. Qed.

Definition ARG_HU : argtab :=
  {| g_istrlen := 0; g_memchr := 0x2bbf28; g_stdio_write := 0x2b55ac; g_exit := 0x2b17ec;
     g_file_lo := 0x31ebd0; g_file_hi := 0x31ee98; g_canary_got := 0x31d588; g_canary := 0x351b28;
     g_ro_lo := 0x3a760; g_ro_hi := 0x3a7a8 |}.
Lemma L_ANL_ARG_HU : @ARG_HU = @AN.ARG_HU.
Proof. unfold ARG_HU. reflexivity. Qed.

Definition ARG_HA : argtab :=
  {| g_istrlen := 0x1d5654; g_memchr := 0x5281e8; g_stdio_write := 0x522984; g_exit := 0x51ce64;
     g_file_lo := 0x5ac5c8; g_file_hi := 0x5ac898; g_canary_got := 0x5a8380; g_canary := 0xbc63b0;
     g_ro_lo := 0x10498; g_ro_hi := 0x104d8 |}.
Lemma L_ANL_ARG_HA : @ARG_HA = @AN.ARG_HA.
Proof. unfold ARG_HA. reflexivity. Qed.

Definition ARG_HB : argtab :=
  {| g_istrlen := 0x1d05c4; g_memchr := 0x560d0c; g_stdio_write := 0x55b4a8; g_exit := 0x555988;
     g_file_lo := 0x5e4f48; g_file_hi := 0x5e5218; g_canary_got := 0x5e0a48; g_canary := 0xbf8ff0;
     g_ro_lo := 0x104b0; g_ro_hi := 0x104f0 |}.
Lemma L_ANL_ARG_HB : @ARG_HB = @AN.ARG_HB.
Proof. unfold ARG_HB. reflexivity. Qed.

Definition ARGTABS : list (Z * argtab) := [(0xe1830, ARG_HU); (0xdcf48, ARG_H0); (0x19a08c, ARG_HA); (0x194ffc, ARG_HB); (0x5f9ac, ARG_A0); (0x5f0a0, ARG_B0)].
Lemma L_ANL_ARGTABS : @ARGTABS = @AN.ARGTABS.
Proof. unfold ARGTABS. rewrite ?L_ANL_ARG_A0, ?L_ANL_ARG_B0, ?L_ANL_ARG_H0, ?L_ANL_ARG_HU, ?L_ANL_ARG_HA, ?L_ANL_ARG_HB. reflexivity. Qed.

Fixpoint argtab_find (e : Z) (l : list (Z * argtab)) : argtab :=
  match l with
  | [] => ARG_B0
  | (k, t) :: r => if Z.eqb e k then t else argtab_find e r
  end.
Lemma L_ANL_argtab_find : @argtab_find = @AN.argtab_find.
Proof. unfold argtab_find. rewrite ?L_ANL_ARG_B0. reflexivity. Qed.

Definition argtab_of (A : atable) : argtab := argtab_find (a_entry A) ARGTABS.
Lemma L_ANL_argtab_of : @argtab_of = @AN.argtab_of.
Proof. unfold argtab_of. rewrite ?L_ANL_ARGTABS, ?L_ANL_argtab_find. reflexivity. Qed.

Definition LMAX : Z := 131071.
Lemma L_ANL_LMAX : @LMAX = @AN.LMAX.
Proof. unfold LMAX. reflexivity. Qed.

Definition TOPNUL : Z := CXLF.p47 - 17.
Lemma L_ANL_TOPNUL : @TOPNUL = @AN.TOPNUL.
Proof. unfold TOPNUL. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition STRLO : Z := 0x7fff80000000 + 192.
Lemma L_ANL_STRLO : @STRLO = @AN.STRLO.
Proof. unfold STRLO. reflexivity. Qed.

Definition arg_idx (args : list expr) : option nat :=
  match args with
  | [ELit 0] => Some 0%nat
  | [ELit 1] => Some 1%nat
  | _ => None
  end.
Lemma L_ANL_arg_idx : @arg_idx = @AN.arg_idx.
Proof. unfold arg_idx. reflexivity. Qed.

Definition str_e (i : nat) : expr := match i with O => e_str0 | _ => e_str1 end.
Lemma L_ANL_str_e : @str_e = @AN.str_e.
Proof. unfold str_e. rewrite ?APCL.L_APCL_e_str0, ?APCL.L_APCL_e_str1. reflexivity. Qed.

Definition len_e (i : nat) : expr := match i with O => EVar V_L0 | _ => EVar V_L1 end.
Lemma L_ANL_len_e : @len_e = @AN.len_e.
Proof. unfold len_e. rewrite ?APCL.L_APCL_V_L0, ?APCL.L_APCL_V_L1. reflexivity. Qed.

Definition blob_of (i : nat) : nat := match i with O => 1%nat | _ => 2%nat end.
Lemma L_ANL_blob_of : @blob_of = @AN.blob_of.
Proof. unfold blob_of. reflexivity. Qed.

Definition nul_e (i : nat) : expr := eadd (str_e i) (len_e i).
Lemma L_ANL_nul_e : @nul_e = @AN.nul_e.
Proof. unfold nul_e. rewrite ?L_ANL_str_e, ?L_ANL_len_e, ?APCL.L_APCL_eadd. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Let G : argtab := argtab_of A.
Definition eeq (k : list kentry) (a b : expr) : bool :=
  expr_eqb a b || (lin_ge0 k [(a, 0)] [(b, 0)] && lin_ge0 k [(b, 0)] [(a, 0)]).
Definition argc_ok (k : list kentry) (i : nat) : bool :=
  match i with
  | O => true
  | _ => match xlo k (EVar V_ARGC) with Some lo => Z.leb 2 lo | None => false end
  end.
Definition str_hi (k : list kentry) (i : nat) : Z :=
  match xlo k (len_e i) with Some lo => TOPNUL - Z.max 0 lo | None => TOPNUL end.
Definition ioff (i : nat) : Z := match i with O => 0 | _ => 1 end.
Definition str_facts (k : list kentry) (i : nat) : list kentry :=
  [KRange (str_e i) (STRLO + ioff i) (str_hi k i); KRange (nul_e i) (STRLO + ioff i) TOPNUL].
Definition srl_facts (k : list kentry) (i : nat) : list kentry :=
  [KRange (mkSrl k (str_e i) 3) (STRLO / 8) (str_hi k i / 8); KRange (mkSrl k (nul_e i) 3) (STRLO / 8) (TOPNUL / 8)].
Definition len_fact (k : list kentry) (i : nat) : list kentry :=
  match xhi k (len_e i) with
  | Some hi => if Z.leb hi LMAX then [] else [KRange (len_e i) 0 LMAX]
  | None => [KRange (len_e i) 0 LMAX]
  end.
Definition strlen_facts1 (k : list kentry) (i : nat) : list kentry :=
  len_fact k i ++ match i with O => [] | _ => str_facts k 1 end ++ str_facts k 0.
Definition strlen_facts2 (k : list kentry) (i : nat) : list kentry :=
  match i with O => [] | _ => srl_facts k 1 end ++ srl_facts k 0.
Definition kimg_cover (k : list kentry) (a b : Z) : bool :=
  existsb (fun K => match K with KImg lo hi => Z.leb lo a && Z.leb b hi | _ => false end) k.
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
Definition node_argmemchr (cs : acs) (args : list expr) : option acs :=
  match arg_idx args, ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some i, Some ret, Some c, Some n =>
      if (Z.eqb (pc cs) (g_memchr G) && eeq (kn cs) (reg cs 10) (str_e i) && Z.eqb c 0
          && Z.leb (LMAX + 8) n && Z.ltb n (CXLF.p63) && argc_ok (kn cs) i
          && kimg_cover (kn cs) (g_ro_lo G) (g_ro_hi G))%bool
      then after_call nx0 cs ret (Some (nul_e i)) (kn cs)
      else None
  | _, _, _, _ => None
  end.
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
Fixpoint find_blob (k : list kentry) (cb : expr) (ck : Z) : option (expr * nat) :=
  match k with
  | [] => None
  | KBlob (SA b o) n bk :: rest => if (expr_eqb b cb && Z.eqb o ck)%bool then Some (n, bk) else find_blob rest cb ck
  | _ :: rest => find_blob rest cb ck
  end.
Definition flush_lit (lit : list Z) (acc : list spiece) : list spiece :=
  match lit with [] => acc | _ => SPLit (rev lit) :: acc end.
Fixpoint pieces_walk (fuel : nat) (k : list kentry) (c wp : expr) (lit : list Z) (acc : list spiece)
  : option (list spiece) :=
  match fuel with
  | O => None
  | S f =>
      if eeq k c wp then Some (rev (flush_lit lit acc)) else
      let '(cb, ck) := split_lit c in
      match (match find_blob k cb ck with
             | Some (n, b) => match foldK k n with ELit 0 => None | n' => Some (n', b) end  
             | None => None
             end) with
      | Some (n', b) =>
          
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
Definition extra_pieces (k : list kentry) (s l : expr) : option (list spiece) :=
  let lz := match l with ELit z => Some (CXLF.zm64 z) | _ => None end in
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
Definition STKMAX : Z := 8388608.
Definition send_ok (k : list kentry) (s l : expr) (shi lhi : Z) : bool :=
  (shi + lhi <=? CXLF.p47)
  || match xhi k (eadd s l) with
     | Some e => (e <=? CXLF.p47) && (shi + lhi <? two64)
     | None => false
     end.
Definition off_lazy (k : list kentry) (b : expr) (n : expr) : bool :=
  (match xhi k (eadd b n), xlo k b with
   | Some hi, Some lo => Z.leb (img_lo A) lo && Z.leb hi (img_hi A)
   | _, _ => false
   end)
  || lin_ge0 k [(b, STKMAX)] [(e_spw, 0)].
Definition node_stdio_write (cs : acs) : option (Z * list spiece * acs) :=
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
            && (0 <=? wblo) && (wphi <=? CXLF.p47)   
            && (nphi + lhi <=? CXLF.p26)
            && kwritable k k qb qk 112
            && (4294967296 + 112 <=? splo) && (sphi <=? CXLF.p47)
            && send_ok k s l shi lhi   
            && lin_ge0 k [(WP, 0)] [(WB, 0)]
            && (lin_ge0 k [(spm, 0)] [(WP, 0)] || lin_ge0 k [(WB, 0)] [(sp, 0)])
            && (lin_ge0 k [(spm, 0)] [(s, 0); (l, 0)] || lin_ge0 k [(s, 0)] [(sp, 0)])
            && lin_ge0 k [(spm, STKMAX)] [(e_spw, 0)] && off_lazy k WB np && (match l with ELit 0 => true | _ => off_lazy k s l end)
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
Definition two63 : Z := CXLF.p63.
Definition node_reldiff (cs : acs) (args : list expr) : option acs :=
  match args with
  | [X; Y; ELit s] =>
      let k := kn cs in
      let '(X', wX) := deand X in let X'' := eaddz X' 0 in   
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
Definition node_srlbound (cs : acs) (args : list expr) : option acs :=
  match args with
  | [e] =>
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
  | _ => None
  end.
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
Definition xe (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  match id with
  | 0%nat => node_stdio_write cs
  | _ => None
  end.
End WithSegs.
Lemma L_ANL_eeq : @eeq = @AN.eeq.
Proof. unfold eeq. rewrite ?AX2L.L_AX2L_expr_eqb, ?AX2L.L_AX2L_lin_ge0. reflexivity. Qed.

Lemma L_ANL_argc_ok : @argc_ok = @AN.argc_ok.
Proof. unfold argc_ok. rewrite ?APCL.L_APCL_V_ARGC, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_ANL_str_hi : @str_hi = @AN.str_hi.
Proof. unfold str_hi. rewrite ?L_ANL_TOPNUL, ?L_ANL_len_e, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_ANL_ioff : @ioff = @AN.ioff.
Proof. unfold ioff. reflexivity. Qed.

Lemma L_ANL_str_facts : @str_facts = @AN.str_facts.
Proof. unfold str_facts. rewrite ?L_ANL_TOPNUL, ?L_ANL_STRLO, ?L_ANL_str_e, ?L_ANL_nul_e, ?L_ANL_str_hi, ?L_ANL_ioff. reflexivity. Qed.

Lemma L_ANL_srl_facts : @srl_facts = @AN.srl_facts.
Proof. unfold srl_facts. rewrite ?L_ANL_TOPNUL, ?L_ANL_STRLO, ?L_ANL_str_e, ?L_ANL_nul_e, ?L_ANL_str_hi, ?AX2L.L_AX2L_mkSrl. reflexivity. Qed.

Lemma L_ANL_len_fact : @len_fact = @AN.len_fact.
Proof. unfold len_fact. rewrite ?L_ANL_LMAX, ?L_ANL_len_e, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_ANL_strlen_facts1 : @strlen_facts1 = @AN.strlen_facts1.
Proof. unfold strlen_facts1. rewrite ?L_ANL_str_facts, ?L_ANL_len_fact. reflexivity. Qed.

Lemma L_ANL_strlen_facts2 : @strlen_facts2 = @AN.strlen_facts2.
Proof. unfold strlen_facts2. rewrite ?L_ANL_srl_facts. reflexivity. Qed.

Lemma L_ANL_kimg_cover : @kimg_cover = @AN.kimg_cover.
Proof. unfold kimg_cover. reflexivity. Qed.

Lemma L_ANL_node_argstrlen : @node_argstrlen = @AN.node_argstrlen.
Proof. unfold node_argstrlen. rewrite ?L_ANL_arg_idx, ?L_ANL_str_e, ?L_ANL_len_e, ?L_ANL_eeq, ?L_ANL_argc_ok, ?L_ANL_strlen_facts1, ?L_ANL_strlen_facts2, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_kn, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_ret_lit, ?APCL.L_APCL_set_pc, ?APCL.L_APCL_set_reg. reflexivity. Qed.

Lemma L_ANL_node_argmemchr : @node_argmemchr = @AN.node_argmemchr.
Proof. unfold node_argmemchr. rewrite ?L_ANL_LMAX, ?L_ANL_arg_idx, ?L_ANL_str_e, ?L_ANL_nul_e, ?L_ANL_eeq, ?L_ANL_argc_ok, ?L_ANL_kimg_cover, ?APCL.L_APCL_after_call, ?APCL.L_APCL_kn, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_reg_lit, ?APCL.L_APCL_ret_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_ANL_node_argnul : @node_argnul = @AN.node_argnul.
Proof. unfold node_argnul. rewrite ?L_ANL_arg_idx, ?L_ANL_nul_e, ?L_ANL_eeq, ?L_ANL_argc_ok, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_kn, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?AX2L.L_AX2L_ridx, ?APCL.L_APCL_set_pc, ?APCL.L_APCL_set_reg, ?AX2L.L_AX2L_two64. reflexivity. Qed.

Lemma L_ANL_node_memcpyarg : @node_memcpyarg = @AN.node_memcpyarg.
Proof. unfold node_memcpyarg. rewrite ?L_ANL_LMAX, ?L_ANL_arg_idx, ?L_ANL_str_e, ?L_ANL_len_e, ?L_ANL_blob_of, ?L_ANL_eeq, ?L_ANL_argc_ok, ?APCL.L_APCL_after_call, ?AX2L.L_AX2L_base_range, ?APCL.L_APCL_e_sp0, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_havoc, ?APCL.L_APCL_kwritable_x, ?AX2L.L_AX2L_lin_ge0, ?APCL.L_APCL_off_image_x, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_ret_lit, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_ANL_find_blob : @find_blob = @AN.find_blob.
Proof. unfold find_blob. rewrite ?AX2L.L_AX2L_expr_eqb. reflexivity. Qed.

Lemma L_ANL_flush_lit : @flush_lit = @AN.flush_lit.
Proof. unfold flush_lit. reflexivity. Qed.

Lemma L_ANL_pieces_walk : @pieces_walk = @AN.pieces_walk.
Proof. unfold pieces_walk. rewrite ?L_ANL_eeq, ?L_ANL_find_blob, ?L_ANL_flush_lit, ?APCL.L_APCL_eadd, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_flat_x, ?AX2L.L_AX2L_foldK, ?APCL.L_APCL_kreadZ, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi. reflexivity. Qed.

Lemma L_ANL_PIECES_FUEL : @PIECES_FUEL = @AN.PIECES_FUEL.
Proof. unfold PIECES_FUEL. reflexivity. Qed.

Lemma L_ANL_extra_pieces : @extra_pieces = @AN.extra_pieces.
Proof. unfold extra_pieces. rewrite ?L_ANL_str_e, ?L_ANL_len_e, ?L_ANL_blob_of, ?L_ANL_eeq, ?L_ANL_argc_ok, ?L_ANL_find_blob, ?APCL.L_APCL_flat_x, ?APCL.L_APCL_kread_bytes, ?AX2L.L_AX2L_split_lit, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_ANL_STKMAX : @STKMAX = @AN.STKMAX.
Proof. unfold STKMAX. reflexivity. Qed.

Lemma L_ANL_send_ok : @send_ok = @AN.send_ok.
Proof. unfold send_ok. rewrite ?APCL.L_APCL_eadd, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_xhi, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_ANL_off_lazy : @off_lazy = @AN.off_lazy.
Proof. unfold off_lazy. rewrite ?L_ANL_STKMAX, ?APCL.L_APCL_e_spw, ?APCL.L_APCL_eadd, ?AX2L.L_AX2L_lin_ge0, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo. reflexivity. Qed.

Lemma L_ANL_node_stdio_write : @node_stdio_write = @AN.node_stdio_write.
Proof. unfold node_stdio_write. rewrite ?L_ANL_pieces_walk, ?L_ANL_PIECES_FUEL, ?L_ANL_extra_pieces, ?L_ANL_STKMAX, ?L_ANL_send_ok, ?L_ANL_off_lazy, ?APCL.L_APCL_after_call, ?APCL.L_APCL_e_spw, ?APCL.L_APCL_eadd, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_esub, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kimg_cut, ?APCL.L_APCL_kn, ?APCL.L_APCL_kn_havoc, ?APCL.L_APCL_kread8e, ?APCL.L_APCL_kreadZ, ?APCL.L_APCL_kwritable, ?AX2L.L_AX2L_lin_ge0, ?APCL.L_APCL_nxt, ?APCL.L_APCL_pc, ?APCL.L_APCL_reg, ?APCL.L_APCL_reg_lit, ?APCL.L_APCL_ret_lit, ?AX2L.L_AX2L_split_lit, ?AX2L.L_AX2L_xhi, ?AX2L.L_AX2L_xlo, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_ANL_two63 : @two63 = @AN.two63.
Proof. unfold two63. rewrite ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Lemma L_ANL_node_reldiff : @node_reldiff = @AN.node_reldiff.
Proof. unfold node_reldiff. rewrite ?L_ANL_two63, ?APCL.L_APCL_add_kn, ?AX2L.L_AX2L_deand, ?APCL.L_APCL_deand, ?APCL.L_APCL_eaddz, ?APCL.L_APCL_esub, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?AX2L.L_AX2L_mkSrl, ?APCL.L_APCL_nxt, ?APCL.L_APCL_xhi1, ?APCL.L_APCL_xlo1. reflexivity. Qed.

Lemma L_ANL_zone_covers : @zone_covers = @AN.zone_covers.
Proof. unfold zone_covers. rewrite ?AX2L.L_AX2L_lin_ge0, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_zlit64. reflexivity. Qed.

Lemma L_ANL_node_zerocover : @node_zerocover = @AN.node_zerocover.
Proof. unfold node_zerocover. rewrite ?L_ANL_zone_covers, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?APCL.L_APCL_nxt, ?AX2L.L_AX2L_split_lit. reflexivity. Qed.

Lemma L_ANL_take_srl : @take_srl = @AN.take_srl.
Proof. unfold take_srl. reflexivity. Qed.

Lemma L_ANL_node_srlbound : @node_srlbound = @AN.node_srlbound.
Proof. unfold node_srlbound. rewrite ?L_ANL_take_srl, ?APCL.L_APCL_add_kn, ?APCL.L_APCL_eadd, ?APCL.L_APCL_escale, ?APCL.L_APCL_expr_vars_lt, ?APCL.L_APCL_kn, ?AX2L.L_AX2L_lin_of, ?APCL.L_APCL_nxt, ?AX2L.L_AX2L_two64, ?AX2L.L_AX2L_unlin, ?APCL.L_APCL_xhi1, ?APCL.L_APCL_xlo1. reflexivity. Qed.

Lemma L_ANL_xn : @xn = @AN.xn.
Proof. unfold xn. rewrite ?L_ANL_node_argstrlen, ?L_ANL_node_argmemchr, ?L_ANL_node_argnul, ?L_ANL_node_memcpyarg, ?L_ANL_node_reldiff, ?L_ANL_node_zerocover, ?L_ANL_node_srlbound. reflexivity. Qed.

Lemma L_ANL_xe : @xe = @AN.xe.
Proof. unfold xe. rewrite ?L_ANL_node_stdio_write. reflexivity. Qed.

End ANL.
