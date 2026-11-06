(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvIT.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DRANGES_A : list (Z * nat) :=
  [ (0x4b40c, 36%nat)  (* [comment removed for export] *)
  ; (0x5cf4c, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf60, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf68, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf6c, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf78, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf7c, 1%nat)  (* [comment removed for export] *)
  ; (0x5cf84, 1%nat)  (* [comment removed for export] *)
  ; (0x5d280, 165%nat)  (* [comment removed for export] *)
  ; (0x5e738, 180%nat)  (* [comment removed for export] *)
  ; (0x5ec80, 156%nat)  (* [comment removed for export] *)
  ; (0x5eef0, 157%nat)  (* [comment removed for export] *)
  ; (0x5f848, 39%nat)  (* [comment removed for export] *)
  ; (0x5f8e4, 690%nat)  (* [comment removed for export] *)
  ; (0x603ac, 45%nat)  (* [comment removed for export] *)
  ; (0x60778, 54%nat)  (* [comment removed for export] *)
  ; (0x6d1d0, 3%nat)  (* [comment removed for export] *)
  ; (0x6ed5c, 2%nat)  (* [comment removed for export] *)
  ; (0x63198, 102%nat)  (* [comment removed for export] *)
  ; (0x7571c, 6%nat)  (* [comment removed for export] *)
  ; (0x7662c, 40%nat)  (* [comment removed for export] *)
  ; (0x809a8, 24%nat)  (* [comment removed for export] *)
  ; (0x80a5c, 13%nat)  (* [comment removed for export] *)
  ; (0x80afc, 7%nat)  (* [comment removed for export] *)
  ; (0x8ca90, 12%nat)  (* [comment removed for export] *)
  ; (0x9d030, 177%nat)  (* [comment removed for export] *)
  ; (0x9d2f4, 1%nat)  (* [comment removed for export] *)
  ; (0x9d2f8, 2%nat)  (* [comment removed for export] *)
  ; (0x9d300, 86%nat)  (* [comment removed for export] *)
  ; (0x9d458, 12%nat)  (* [comment removed for export] *)
  ; (0x9d488, 18%nat)  (* [comment removed for export] *)
  ; (0xed580, 18%nat)  (* [comment removed for export] *)
  ; (0xed9b8, 3%nat)  (* [comment removed for export] *)
  ; (0xeda94, 7%nat)  (* [comment removed for export] *)
  ; (0xedae0, 50%nat)  (* [comment removed for export] *)
  ; (0xedba8, 1%nat)  (* [comment removed for export] *)
  ; (0xedbac, 50%nat)  (* [comment removed for export] *)
  ; (0xedc74, 1%nat)  (* [comment removed for export] *)
  ; (0xedc78, 19%nat)  (* [comment removed for export] *)
  ; (0xedcc4, 29%nat)  (* [comment removed for export] *)
  ; (0xedf38, 57%nat)  (* [comment removed for export] *)
  ; (0xee01c, 14%nat)  (* [comment removed for export] *)
  ; (0xf3fb0, 21%nat)  (* [comment removed for export] *)
  ; (0xf3bec, 105%nat)  (* [comment removed for export] *)
  ; (0xf4004, 78%nat)  (* [comment removed for export] *)
  ; (0xf413c, 46%nat)  (* [comment removed for export] *)
  ; (0xf41f4, 12%nat)  (* [comment removed for export] *)
  ; (0xf34bc, 1%nat)  (* [comment removed for export] *)
  ; (0xf4498, 108%nat)  (* [comment removed for export] *)
  ; (0xf4648, 908%nat)  (* [comment removed for export] *)
  ; (0xf5478, 16%nat)  (* [comment removed for export] *)
  ; (0xf54b8, 61%nat)  (* [comment removed for export] *)
  ; (0xf9c24, 7%nat)  (* [comment removed for export] *)
  ; (0xf42f8, 40%nat)  (* [comment removed for export] *)
  ; (0xfc814, 17%nat)  (* [comment removed for export] *)
  ; (0xfc940, 162%nat)  (* [comment removed for export] *)
  ; (0xfcbc8, 29%nat)  (* [comment removed for export] *)
  ; (0xfcc3c, 9%nat)  (* [comment removed for export] *)
  ; (0xfcc60, 1%nat)  (* [comment removed for export] *)
  ; (0x101694, 21%nat)  (* [comment removed for export] *)
  ; (0x101774, 13%nat)  (* [comment removed for export] *) ].
Definition ITA : itab := mk_itab_ranges BSEGS DRANGES_A.
Lemma ITA_ok : itab_sound BSEGS ITA.
Proof. apply APS.mk_itab_ranges_sound. Qed.
End BoDrvIT.
Require LinuxProcessSemantics.Riscv.Instr OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDrvNodesP.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2B. Import APC. Import AP.
Open Scope Z_scope.

Module DNA.

(* [comment removed for export] *)
Definition X_ISTRLEN : Z := 0x80afc.       (* [comment removed for export] *)
Definition X_REGION : Z := 0x70a08.        (* [comment removed for export] *)
Definition X_STDIO_WRITE : Z := 0xf360c.   (* [comment removed for export] *)
Definition X_MEMCHR : Z := 0xfbe8c.        (* [comment removed for export] *)
Definition X_MODULE_DTOR : Z := 0xc5cd0.
   (* [comment removed for export] *)
Definition X_FUZZ : Z := 0x9d4d0.          (* [comment removed for export] *)
Definition STDOUT_F : Z := 0x10a6b8.
Definition STDERR_F : Z := 0x10a5c8.
Definition IMG_LO : Z := 0x10000.
Definition IMG_HI : Z := 0x663000.
Definition LOWSH_LO : Z := SB + IMG_LO / 8.
Definition LOWSH_HI : Z := SB + IMG_HI / 8.
Definition two64 : Z := 2 ^ 64.
(* [comment removed for export] *)
Definition QC_PRINTF : Z * Z * nat * nat * list nat := (0x5fe1c, 0x5fd70, 22%nat, 23%nat, [1%nat]).            (* [comment removed for export] *)
Definition QC_STRNLEN : Z * Z * nat * nat * list nat := (0x5d2fc, 0x5d344, 18%nat, 9%nat, [1; 18; 22]%nat).  (* [comment removed for export] *)
Definition QC_MEMCHR : Z * Z * nat * nat * list nat := (0x5e7ac, 0x5e7f4, 18%nat, 9%nat, [1; 18; 21]%nat).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CLOB : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

Section WithTables.
Variable segs : list MemImageType.Segment.
Variable nx0 : nat.
Variable G : gtable.

Definition has_fact (k : list kentry) (K : kentry) : bool := existsb (kentry_eqb K) k.
Definition havoc_scratch (k : list kentry) (sp : expr) (n : Z) : list kentry :=
  let '(spb, spk) := split_lit sp in kn_havoc k spb (spk - n) (ELit n).

(* [comment removed for export] *)
Definition leaf_ok (entry : Z) (cs : acs) : option Z :=
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with Some ra => if fresh_ok nx0 cs then Some ra else None | None => None end.
(* [comment removed for export] *)
Definition leaf_ret (cs : acs) (k' : list kentry) (rv : expr) (ra : Z) (cl : list nat) : option acs :=
  node_havoc nx0 (set_pc (set_reg (set_kn cs k') 10 rv) ra) cl.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition argv_blob (j : nat) : bool := (Nat.eqb j 1 || Nat.eqb j 2)%bool.
Definition blob_at (k : list kentry) (s : expr) : option (expr * nat) :=
  let '(sb, sk) := split_lit s in
  match List.find (fun K => match K with KBlob (SA b o) _ _ => expr_eqb b sb && Z.eqb o sk | _ => false end) k with
  | Some (KBlob _ L j) =>
      if (argv_blob j && has_fact k (KWord (let '(b, o) := split_lit (eadd s L) in SA b o) 1 (ELit 0)))%bool then Some (L, j) else None
  | _ =>
      (* [comment removed for export] *)
      if has_fact k (KWord (SA sb sk) 1 (ELit 0)) then Some (ELit 0, 0%nat) else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition str_nowrap (k : list kentry) (s L : expr) (extra : Z) : bool :=
  match xhi k s, xhi k L with Some sh, Some lh => Z.ltb (sh + lh + extra) two64 | _, _ => false end.
(* [comment removed for export] *)
Fixpoint kimg_cov (k : list kentry) (lo hi : Z) : bool :=
  match k with
  | [] => false
  | KImg l h :: rest => (Z.leb l lo && Z.leb hi h) || kimg_cov rest lo hi
  | _ :: rest => kimg_cov rest lo hi
  end%bool.
(* [comment removed for export] *)
Fixpoint lit_strlen (fuel : nat) (k : list kentry) (a : Z) (n : Z) : option Z :=
  match fuel with
  | O => None
  | S f => match kreadZ segs k (ELit 0) (a + n) 1 with
           | Some z => if Z.eqb (z mod 256) 0 then Some n else lit_strlen f k a (n + 1)   (* [comment removed for export] *)
           | None => None
           end
  end.
Definition node_blobstrlen (cs : acs) : option acs :=
  match leaf_ok X_ISTRLEN cs with
  | None => None
  | Some ra =>
      match reg cs 10 with
      | ELit a => match lit_strlen 80 (kn cs) (a mod two64) 0 with
                  | Some n => if Z.ltb (a mod two64 + 81) two64 then leaf_ret cs (kn cs) (ELit n) ra [11; 12]%nat else None
                  | None => None
                  end
      | _ => match blob_at (kn cs) (reg cs 10) with
             | Some (L, _) => if str_nowrap (kn cs) (reg cs 10) L 1 then leaf_ret cs (kn cs) L ra [11; 12]%nat else None
             | None => None
             end
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_readable_al (k : list kentry) (s L : expr) : bool :=
  let '(sb, sk) := split_lit s in
  existsb (fun F => match F with
                    | KUnk (SA fb fo) fl =>
                        let e := eadd (eaddz fb fo) fl in
                        if existsb (fun K => match K with KAlign e' 8 => expr_eqb e' e | _ => false end) k
                        then match xlo k e with
                             | Some lo => if Z.leb 1 lo then xinside k sb sk (eaddz L 1) fb fo fl else false
                             | None => false
                             end
                        else false
                    | _ => false
                    end) k.
Definition MEMCHR_C1 : Z := 0x103e0.       (* [comment removed for export] *)
Definition MEMCHR_C2 : Z := 0x10400.       (* [comment removed for export] *)
Definition node_blobmemchr (cs : acs) : option acs :=
  match leaf_ok X_MEMCHR cs with
  | None => None
  | Some ra =>
      let k := kn cs in let s := reg cs 10 in
      match reg_lit cs 11, reg_lit cs 12, blob_at k s with
      | Some 0, Some n, Some (L, _) =>
          match xhi k L with
          | Some lh =>
              let '(sb, sk) := split_lit s in
              if (Z.leb (lh + 8) n && Z.ltb n two64
                  && (if kn_readable_x k sb sk (eaddz L 8) then true else kn_readable_al k s L)   (* [comment removed for export] *)
                  && str_nowrap k s L 8
                  && kimg_cov k MEMCHR_C1 (MEMCHR_C1 + 8) && kimg_cov k MEMCHR_C2 (MEMCHR_C2 + 8))%bool   (* [comment removed for export] *)
              then leaf_ret cs k (eadd s L) ra CLOB else None
          | None => None
          end
      | _, _, _ => None
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_RIP : Z := 80.
Definition RIP_CLOB : list nat := [5; 11; 12; 13; 14; 15; 16; 17]%nat.
Definition KHIMEM : Z := 0x10007fff8000.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition M2S_CELLS : list (Z * Z) :=
  [(0x105f18, 0x10e1b8); (0x105f20, 0x10eea8); (0x105f28, 0x10eeb0); (0x105f30, 0x10eea0); (0x10e1b8, 0x7fff8000)].
Definition m2s_ok (k : list kentry) : bool :=
  forallb (fun c => match kreadZ segs k (ELit 0) (fst c) 8 with Some z => Z.eqb z (snd c) | None => false end) M2S_CELLS.
(* [comment removed for export] *)
Definition rip_range_ok (nmin slack : Z) (k : list kentry) (beg n : expr) : bool :=
  match xlo k n, xhi k n, xlo k beg, xhi k beg with
  | Some nlo, Some nhi, Some blo, Some bhi =>
      (Z.leb nmin nlo && Z.leb nhi (2 ^ 43)
       && ((Z.leb KHIMEM blo && (Z.leb 1 slack || Z.ltb (bhi + nhi) two47))   (* [comment removed for export] *)
           || Z.leb (bhi + nhi) 0x7fff7fff))%bool                               (* [comment removed for export] *)
  | _, _, _, _ => false
  end.
(* [comment removed for export] *)
Definition rip_stack_ok (cs : acs) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  (kwritable_x k k spb (spk - FR_RIP) (ELit FR_RIP)
   && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - FR_RIP) (ELit FR_RIP)
   && match xlo k sp with Some lo => Z.leb (KHIMEM + 80) lo | None => false end
   && match xhi k sp with Some hi => Z.leb (hi + 16) two47 | None => false end)%bool.
Definition node_region (cs : acs) : option acs :=
  match call_ok_stk nx0 G FR_RIP X_REGION cs with
  | None => None
  | Some ra =>
      let k := kn cs in let '(pb, pk) := split_lit (reg cs 10) in let n := reg cs 11 in
      if (kshok_x k pb pk n && rip_range_ok 8 0 k (reg cs 10) n && rip_stack_ok cs && m2s_ok k)%bool
      then node_havoc nx0 (set_pc (set_reg (set_kn cs (havoc_scratch k (reg cs 2) FR_RIP)) 10 (ELit 0)) ra) RIP_CLOB
      else None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kshok_al (k : list kentry) (beg n : expr) : bool :=
  let '(hb, hk) := split_lit (eaddz beg (-63)) in
  existsb (fun F => match F with
                    | KShOk (SA fb fo) fl =>
                        if existsb (fun K => match K with KAlign e 64 => expr_eqb e (eadd (eaddz fb fo) fl) | _ => false end) k
                        then xinside k hb hk (eaddz n 64) fb fo fl else false
                    | _ => false
                    end) k.
Definition node_qctail (site : Z * Z * nat * nat * list nat) (keep_a0 : bool) (cs : acs) : option acs :=
  let '(from, to, rb, rn, xclob) := site in
  if negb (Z.eqb (pc cs) from && fresh_ok nx0 cs)%bool then None else
  let k := kn cs in let beg := reg cs rb in let n := reg cs rn in
  let '(hb, hk) := split_lit (eaddz beg (-63)) in
  match xlo k n, xhi k n with
  | Some nlo, Some nhi =>
      if (Z.leb 1 nlo && (if kshok_x k hb hk (eaddz n 126) then true else kshok_al k beg n) && m2s_ok k      (* [comment removed for export] *)
          (* [comment removed for export] *)
          && (Z.leb nhi 64 || (rip_range_ok 1 63 k beg n && rip_stack_ok cs)))%bool
      then node_havoc nx0 (set_pc (set_kn cs (havoc_scratch k (reg cs 2) FR_RIP)) to)
                      ((if keep_a0 then [] else [10%nat]) ++ CLOB ++ xclob)
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition DTOR_P_START : Z := 0x10a8c0.
Definition DTOR_FLAG : Z := 0x10ab00.      (* [comment removed for export] *)
Definition DTOR_MU : Z := 0x10ba70.        (* [comment removed for export] *)
Definition DTOR_GLOBS : list (Z * Z) :=
  [(0x22ae0, 0x20); (0x22b00, 0x20); (0x22b20, 0x40); (0x22b60, 0x20); (0x26940, 0x60);
   (0x269a0, 0x60); (0x26a00, 0x20); (0x26a20, 0x60); (0x26a80, 0x40)].      (* [comment removed for export] *)
Fixpoint dtor_desc_cells (p : Z) (gs : list (Z * Z)) : list (Z * nat * Z) :=
  match gs with
  | [] => []
  | (b, s) :: r => (p, 8%nat, b) :: (p + 16, 8%nat, s) :: (p + 56, 8%nat, two64 - 1) :: dtor_desc_cells (p + 64) r
  end.
Definition DTOR_CELLS : list (Z * nat * Z) :=
  [(0x106ba8, 8%nat, DTOR_P_START); (0x106bb0, 8%nat, DTOR_P_START + 64 * 9); (0x10ab00, 8%nat, 1); (0x105f10, 8%nat, 0x10b9b8);
   (0x10b9d0, 4%nat, 1); (0x10ee98, 1%nat, 1);
   (0x105f18, 8%nat, 0x10e1b8); (0x10e1b8, 8%nat, 0x7fff8000); (0x105f20, 8%nat, 0x10eea8); (0x105f28, 8%nat, 0x10eeb0); (0x105f30, 8%nat, 0x10eea0);
   (0x105f38, 8%nat, 0x107e58); (0x107e58, 8%nat, 0xfc38c); (0x105f08, 8%nat, 0x19fce8); (0x19fd60, 8%nat, two64 - 1)]
  ++ dtor_desc_cells DTOR_P_START DTOR_GLOBS.
Definition dtor_cells_ok (k : list kentry) : bool :=
  (forallb (fun c => match kreadZ segs k (ELit 0) (fst (fst c)) (snd (fst c)) with Some z => Z.eqb z (snd c) | None => false end) DTOR_CELLS
   && match kreadZ segs k (ELit 0) 0x105ef8 8, kreadZ segs k (ELit 0) 0x10468 8 with Some _, Some _ => true | _, _ => false end
   && forallb (fun g => kn_readable_x k (ELit 0) (0x7fff8000 + fst g / 8) (ELit (snd g / 8))) ((DTOR_P_START, 64 * 9) :: DTOR_GLOBS))%bool.
Definition dtor_sp_ok (cs : acs) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  (kwritable_x k k spb (spk - 512) (ELit 512)
   && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - 512) (ELit 512)
   && match xlo k sp, xhi k sp with Some lo, Some hi => (Z.leb (KHIMEM + 512) lo && Z.leb (hi + 16) two47)%bool | _, _ => false end)%bool.
Definition node_module_dtor (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) X_MODULE_DTOR) then None else
  match ret_lit cs with
  | Some ra =>
      if negb (dtor_sp_ok cs && fresh_ok nx0 cs && dtor_cells_ok (kn cs))%bool then None else
      (* [comment removed for export] *)
      let k0 := kn_havoc (kn_havoc (kn_havoc (kn cs) (ELit 0) LOWSH_LO (ELit (LOWSH_HI - LOWSH_LO))) (ELit 0) DTOR_FLAG (ELit 8))
                         (ELit 0) DTOR_MU (ELit 8) in
      node_havoc nx0 (set_pc (set_kn cs (havoc_scratch k0 (reg cs 2) 512)) ra) (10%nat :: CLOB)
  | None => None
  end.

(* [comment removed for export] *)
Definition at_sys (cs : acs) (nr : Z) : bool :=
  (is_ecall_at segs cs && match reg_lit cs 17 with Some z => Z.eqb z nr | None => false end)%bool.
Definition reg_is (cs : acs) (r : nat) (z : Z) : bool :=
  match reg_lit cs r with Some z' => Z.eqb z' z | None => false end.
Definition node_ioctl (cs : acs) : option acs :=
  if (at_sys cs 29 && reg_is cs 10 1 && reg_is cs 11 0x5413)%bool
  then Some (set_pc (set_reg cs 10 (ELit (two64 - 25))) (pc cs + 4)) else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition flush_lit (acc : list Z) (ps : list spiece) : list spiece := match acc with [] => ps | _ => ps ++ [SPLit (rev acc)] end.
(* [comment removed for export] *)
Definition blob_litlen (k : list kentry) (j : nat) : option Z :=
  match List.find (fun K => match K with KBlob _ _ j' => Nat.eqb j' j | _ => false end) k with
  | Some (KBlob _ L _) => match xlo k L, xhi k L with Some lo, Some hi => if Z.eqb lo hi then Some lo else None | _, _ => None end
  | _ => None
  end.
(* [comment removed for export] *)
Fixpoint eblob_run (fuel : nat) (k : list kentry) (b : expr) (o : Z) (j : nat) (i : Z) (n : Z) : option Z :=
  match fuel with
  | O => None
  | S f =>
      if Z.leb n i then (if Z.eqb n i then Some o else None) else
      match List.find (fun K => match K with KWord (SA kb ko) w (EBlob false j' i' w') => expr_eqb kb b && Z.eqb ko o && Nat.eqb j' j && Z.eqb i' i && Nat.eqb w w' | _ => false end) k with   (* [comment removed for export] *)
      | Some (KWord _ w _) => eblob_run f k b (o + Z.of_nat w) j (i + Z.of_nat w) n
      | _ => None
      end
  end.
(* [comment removed for export] *)
Definition pos_eq (k : list kentry) (b : expr) (o : Z) (sb : expr) (so : Z) : bool :=
  ((expr_eqb b sb && Z.eqb o so) || (lin_ge0 k [(b, o)] [(sb, so)] && lin_ge0 k [(sb, so)] [(b, o)]))%bool.
Fixpoint pieces_walk (fuel : nat) (k : list kentry) (b : expr) (o : Z) (sb : expr) (so : Z) (acc : list Z) (ps : list spiece)
  : option (list spiece) :=
  match fuel with
  | O => None
  | S f =>
      if pos_eq k b o sb so then Some (flush_lit acc ps) else
      match List.find (fun K => match K with KBlob (SA kb ko) _ _ => expr_eqb kb b && Z.eqb ko o | _ => false end) k with
      | Some (KBlob _ ne j) =>
          let '(b', o') := split_lit (eadd (eaddz b o) ne) in
          if bflat_x k b' o' (ELit 0)          (* [comment removed for export] *)
          then pieces_walk f k b' o' sb so [] (flush_lit acc ps ++ [SPBlob j]) else None
      | _ =>
          match kreadZ segs k b o 1 with
          | Some z => pieces_walk f k b (o + 1) sb so (z :: acc) ps
          | None =>
              (* [comment removed for export] *)
              match List.find (fun K => match K with KWord (SA kb ko) _ (EBlob false _ 0 _) => expr_eqb kb b && Z.eqb ko o | _ => false end) k with
              | Some (KWord _ _ (EBlob _ j _ _)) =>
                  match blob_litlen k j with
                  | Some n => match eblob_run 600 k b o j 0 n with
                              | Some o' => pieces_walk f k b o' sb so [] (flush_lit acc ps ++ [SPBlob j])
                              | None => None
                              end
                  | None => None
                  end
              | _ => None
              end
          end
      end
  end.
Definition range_pieces (k : list kentry) (from to : expr) : option (list spiece) :=
  let '(fb, fo) := split_lit from in let '(tb, tk) := split_lit to in
  if bflat_x k fb fo (ELit 0) then pieces_walk 600 k fb fo tb tk [] [] else None.
Definition FR_SW : Z := 112.
(* [comment removed for export] *)
Definition SSP_GOT : Z := 0x106c60.         (* [comment removed for export] *)
Definition SSP_CELL : Z := 0x6613c0.       (* [comment removed for export] *)
Definition ssp_ok (k : list kentry) : bool :=
  (kimg_cov k SSP_GOT (SSP_GOT + 8) && match kread8e segs k (ELit 0) SSP_CELL with Some _ => true | None => false end)%bool.
(* [comment removed for export] *)
Definition sw_sp_ok (cs : acs) : bool :=
  let k := kn cs in let sp := reg cs 2 in let '(spb, spk) := split_lit sp in
  (kwritable_x k k spb (spk - FR_SW) (ELit FR_SW)
   && in_floor k (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - FR_SW) (ELit FR_SW)
   && match xlo k sp, xhi k sp with Some lo, Some hi => (Z.leb (4294967296 + FR_SW) lo && Z.leb hi two47)%bool | _, _ => false end)%bool.
(* [comment removed for export] *)
Definition blob_len_hi (k : list kentry) (j : nat) : option Z :=
  match List.find (fun K => match K with KBlob _ _ j' => Nat.eqb j' j | _ => false end) k with
  | Some (KBlob _ L _) => xhi k L
  | _ => None
  end.
Fixpoint pieces_len_hi (k : list kentry) (ps : list spiece) : option Z :=
  match ps with
  | [] => Some 0
  | SPLit zs :: r => match pieces_len_hi k r with Some h => Some (Z.of_nat (length zs) + h) | None => None end
  | SPBlob j :: r => match blob_len_hi k j, pieces_len_hi k r with Some a, Some h => Some (a + h) | _, _ => None end
  end.
(* [comment removed for export] *)
Definition sw_range_ok (k : list kentry) (from to : expr) (ps : list spiece) (spb : expr) (spk : Z) : bool :=
  match pieces_len_hi k ps, xhi k from, xhi2 k to with
  | Some h, Some fh, Some th =>
      let '(fb, fo) := split_lit from in
      (Z.leb h (2 ^ 29) && Z.ltb (fh + 2 ^ 29) two64 && Z.leb th two47
       && disj_x k fb fo (ELit h) spb (spk - FR_SW) (ELit FR_SW))%bool
  | _, _, _ => false
  end.
Definition node_stdio_write (cs : acs) : option (Z * list spiece * acs) :=
  if negb (Z.eqb (pc cs) X_STDIO_WRITE && fresh_ok nx0 cs && sw_sp_ok cs && ssp_ok (kn cs))%bool then None else
  let k := kn cs in
  match reg_lit cs 10, ret_lit cs with
  | Some f, Some ra =>
      if negb (Z.eqb f STDOUT_F || Z.eqb f STDERR_F)%bool then None else
      match kreadZ segs k (ELit 0) (f + 120) 4, kread8e segs k (ELit 0) (f + 88), kreadZ segs k (ELit 0) (f + 96) 8,
            kread8e segs k (ELit 0) (f + 56), kread8e segs k (ELit 0) (f + 40) with
      | Some fd, Some bufe, Some bsz, Some wbe, Some wpe =>
          match range_pieces k wbe wpe, range_pieces k (reg cs 11) (eadd (reg cs 11) (reg cs 12)) with
          | Some pend, Some ext =>
              let '(spb, spk) := split_lit (reg cs 2) in
              if negb (((Z.eqb fd 1 && Z.eqb f STDOUT_F) || (Z.eqb fd 2 && Z.eqb f STDERR_F))        (* [comment removed for export] *)
                       && sw_range_ok k wbe wpe pend spb spk && sw_range_ok k (reg cs 11) (eadd (reg cs 11) (reg cs 12)) ext spb spk)%bool then None else
              let k1 := havoc_scratch k (reg cs 2) FR_SW in
              let k2 := KWord (SA (ELit 0) (f + 40)) 8 bufe :: KWord (SA (ELit 0) (f + 56)) 8 bufe
                        :: KWord (SA (ELit 0) (f + 32)) 8 (eaddz bufe bsz)
                        :: kn_havoc (kn_havoc (kn_havoc k1 (ELit 0) (f + 40) (ELit 8)) (ELit 0) (f + 56) (ELit 8)) (ELit 0) (f + 32) (ELit 8) in
              match node_havoc nx0 (set_pc (set_reg (set_kn cs k2) 10 (reg cs 12)) ra) CLOB with
              | Some cs' => Some (fd, pend ++ ext, cs')
              | None => None
              end
          | _, _ => None
          end
      | _, _, _, _, _ => None
      end
  | _, _ => None
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ret_with (cs : acs) (r : expr) (k : list kentry) (nx : nat) (f : afd) : acs :=
  let ss := a_ss cs in
  ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 r) k nx)
      (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) f (a_tidset cs) (a_meter cs) (a_fake cs) (a_fbud cs).
Definition ret_simple (cs : acs) (r : expr) : acs := ret_with cs r (kn cs) (nxt cs) (a_fd cs).
Definition is_std (f : afd) : bool := match f with FdStd => true | _ => false end.
Definition AT_FDCWD64 : Z := two64 - 100.
Definition O_FLAGS : Z := 32768.            (* [comment removed for export] *)
Definition CHZ : Z := 65536.
Definition FCAP : Z := 2 ^ 26.
Definition CHUNKB : nat := 3%nat.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition openat_ok (args : list expr) (cs : acs) : option expr :=
  match args with
  | path :: _ =>
      if (at_sys cs 56 && reg_is cs 10 AT_FDCWD64 && expr_eqb (reg cs 11) path && reg_is cs 12 O_FLAGS && is_std (a_fd cs)
          (* [comment removed for export] *)
          && match acs_floor (a_maps cs) with None => true | Some _ => false end && Z.leb 4096 (a_ylo cs)
          && match xlo (kn cs) (a_brk cs) with Some l => Z.ltb 0 l | None => false end
          && lin_ge0 (kn cs) [(path, 0)] [(a_brk cs, 0)])%bool
      then match blob_at (kn cs) path with
           | Some (L, j) =>
               (* [comment removed for export] *)
               if ((Nat.eqb j 2 || Nat.eqb j 0)
                   && match xhi (kn cs) path, xhi (kn cs) L with Some hp, Some hl => Z.ltb (hp + hl + 4104) two64 | _, _ => false end)%bool
               then Some L else None
           | None => None
           end
      else None
  | _ => None
  end.
(* [comment removed for export] *)
Definition node_openat_toolong (args : list expr) (cs : acs) : option acs :=
  match openat_ok args cs with
  | Some L => match xlo (kn cs) L with Some lo => if Z.leb 4096 lo then Some (ret_simple cs (ELit (two64 - 36))) else None | None => None end
  | None => None
  end.
(* [comment removed for export] *)
Definition path_len_ok (cs : acs) (L : expr) : bool :=
  match xlo (kn cs) L, xhi (kn cs) L with Some lo, Some hi => (Z.leb 1 lo && Z.leb hi 4095)%bool | _, _ => false end.
Definition path_len_ok0 (cs : acs) (L : expr) : bool :=
  match xlo (kn cs) L, xhi (kn cs) L with Some lo, Some hi => (Z.leb 0 lo && Z.leb hi 4095)%bool | _, _ => false end.
(* [comment removed for export] *)
Definition CLS_ABSENT : Z := 2 ^ 26 + 1.
Definition CLS_DIR : Z := 2 ^ 26 + 2.
Definition cls_is (k : list kentry) (c : Z) : bool :=
  match xlo k (EVar 4), xhi k (EVar 4) with Some lo, Some hi => (Z.eqb lo c && Z.eqb hi c)%bool | _, _ => false end.
Definition node_openat_absent (args : list expr) (cs : acs) : option acs :=
  match openat_ok args cs with
  | Some L => if (path_len_ok0 cs L && cls_is (kn cs) CLS_ABSENT)%bool then Some (ret_simple cs (ELit (two64 - 2))) else None
  | None => None
  end.
(* [comment removed for export] *)
Definition openat_err_child (cs : acs) : acs :=
  let v := nxt cs in ret_with cs (EVar v) (KRange (EVar v) (two64 - 4095) (two64 - 1) :: kn cs) (S v) FdStd.
(* [comment removed for export] *)
Definition node_openat_file2 (args : list expr) (cs : acs) : option (acs * acs) :=
  match args, openat_ok args cs with
  | _ :: lenE :: _, Some L =>
      (* [comment removed for export] *)
      if (path_len_ok cs L && fresh_ok nx0 cs && expr_eqb lenE (EVar 4) && expr_vars_lt (nxt cs) lenE
          && match xlo (kn cs) lenE, xhi (kn cs) lenE with Some lo, Some hi => Z.leb 0 lo && Z.leb hi FCAP | _, _ => false end)%bool
      then Some (openat_err_child cs, ret_with cs (ELit 3) (kn cs) (nxt cs) (FdFile CHUNKB lenE (ELit 0)))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_openat_dir2 (args : list expr) (cs : acs) : option (acs * acs) :=
  match openat_ok args cs with
  | Some L => if (path_len_ok cs L && fresh_ok nx0 cs && cls_is (kn cs) CLS_DIR)%bool then Some (openat_err_child cs, ret_with cs (ELit 3) (kn cs) (nxt cs) FdDir) else None
  | None => None
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dst_ok (cs : acs) (n : expr) : option (expr * Z) :=
  let k := kn cs in let '(db, dk) := split_lit (reg cs 11) in
  match reg cs 11, xhi k n with
  | ELit d, Some nh =>
      if (flat_x k db dk n && kwritable_x k k db dk n && Z.leb (g_img_lo G) d && Z.leb (d + nh) (g_img_hi G) && Z.leb 0 nh
          && existsb (fun w => match fst w, snd w with ELit wb, ELit wn => Z.leb 0 wb && Z.leb 0 wn && Z.ltb (wb + wn) two64 && Z.leb wb d && Z.leb (d + nh) (wb + wn) | _, _ => false end) (a_ghost cs))%bool
      then Some (db, dk) else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_read (cs : acs) : option acs :=
  let k := kn cs in
  match a_fd cs with
  | FdFile kb len off =>
      if negb (at_sys cs 63 && reg_is cs 10 3)%bool then None else
      let cnt := reg cs 12 in
      match dst_ok cs cnt, xlo2 k cnt, xhi2 k cnt with
      | Some (db, dk), Some clo, Some chi =>
          if negb (Z.leb 1 clo && Z.leb chi CHZ)%bool then None else
          let rem := esub len off in
          let exact := match xhi2 k len with Some lh => Z.ltb lh FCAP | None => false end in
          (* [comment removed for export] *)
          let blobf (n : expr) := match lit_of off, lit_of cnt with
                                  | Some zo, Some zc => if (Z.eqb zo 0 && Z.eqb zc 65536)%bool then [KBlob (SA db dk) n kb] else []
                                  | _, _ => [] end in
          match xlo2 k rem, xhi2 k rem with
          | Some rlo, Some rhi =>
              if (Z.eqb rlo 0 && Z.eqb rhi 0 && exact)%bool then Some (ret_simple cs (ELit 0))
              else if (Z.leb chi rlo || lin_ge0 k [(rem, 0)] [(cnt, 0)])%bool then                                   (* [comment removed for export] *)
                Some (ret_with cs cnt (blobf cnt ++ kn_havoc k db dk cnt) (nxt cs) (FdFile kb len (eadd off cnt)))
              else if (Z.leb 1 rlo && (Z.ltb rhi clo || lin_ge0 k [(cnt, -1)] [(rem, 0)]) && exact)%bool then      (* [comment removed for export] *)
                Some (ret_with cs rem (blobf rem ++ kn_havoc k db dk cnt) (nxt cs) (FdFile kb len len))
              else None
          | _, _ => None
          end
      | _, _, _ => None
      end
  | FdDir => if (at_sys cs 63 && reg_is cs 10 3
                 && match dst_ok cs (reg cs 12), xlo k (reg cs 12), xhi k (reg cs 12) with
                    | Some _, Some l, Some h => Z.leb 1 l && Z.leb h CHZ | _, _, _ => false end)%bool
             then Some (ret_simple cs (ELit (two64 - 21))) else None
  | FdStd => None
  end.
(* [comment removed for export] *)
Definition node_close (cs : acs) : option acs :=
  if (at_sys cs 57 && reg_is cs 10 3 && negb (is_std (a_fd cs)))%bool then Some (ret_with cs (ELit 0) (kn cs) (nxt cs) FdStd) else None.

(* [comment removed for export] *)
Definition XNP (xn : nat -> list expr -> acs -> option acs) (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 61 then node_read cs
  else if Nat.eqb id 62 then node_close cs
  else if Nat.eqb id 63 then node_ioctl cs
  else if Nat.eqb id 67 then node_blobmemchr cs
  else if Nat.eqb id 68 then node_blobstrlen cs
  else if Nat.eqb id 69 then node_region cs
  else if Nat.eqb id 71 then node_qctail QC_PRINTF false cs
  else if Nat.eqb id 72 then node_qctail QC_STRNLEN true cs
  else if Nat.eqb id 73 then node_qctail QC_MEMCHR true cs
  else if Nat.eqb id 604 then node_openat_toolong args cs
  else if Nat.eqb id 606 then node_openat_absent args cs
  else xn id args cs.
(* [comment removed for export] *)
Definition XAP (xa : nat -> list expr -> acs -> option (acs * acs)) (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
  if Nat.eqb id 602 then node_openat_file2 args cs
  else if Nat.eqb id 603 then node_openat_dir2 args cs
  else xa id args cs.
Definition XEP (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
  if Nat.eqb id 64 then node_stdio_write cs else None.
(* [comment removed for export] *)
End WithTables.
End DNA.
End BoDrvNodesP.
Require Stdlib.micromega.Lia LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoFZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.Bool.Bool Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module FuzzN.
Definition ENTRY : Z := 0x9d4d0.
Definition RETPC : Z := 0x9da94.
Definition NINSTR : nat := 505%nat.            (* [comment removed for export] *)

Definition SZHI : Z := 2 ^ 26 - 1.
Definition FR : Z := 224.                       (* [comment removed for export] *)
Definition B2JYLO : Z := 2 ^ 17.                (* [comment removed for export] *)
Definition YLO : Z := FR + B2JYLO.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition TP : expr := ELit (g_tp GBOTH).
Definition regsT : list expr := sr_upd regs0 4 TP.    (* [comment removed for export] *)
Definition DATA : expr := EVar 9.      (* [comment removed for export] *)
Definition SIZE : expr := EVar 10.     (* [comment removed for export] *)
Definition e_mtr : expr := EVar 31.    (* [comment removed for export] *)
Definition e_fb : expr := EVar 32.     (* [comment removed for export] *)
Definition NXF : nat := 33.

(* [comment removed for export] *)
Definition MTRGROW : Z := 2 ^ 36.              (* [comment removed for export] *)
Definition MTRIN : Z := 2 ^ 38 + 2 ^ 37.        (* [comment removed for export] *)
Definition FBNEED : Z := 264.                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition data_facts : list kentry :=
  [ KRange SIZE 1 SZHI; KRange (eaddz (escale 2 SIZE) (-2)) 0 (2 * SZHI - 2);   (* [comment removed for export] *)
    KRange DATA PTRLO (PTRHI - 1); KRange (eadd DATA SIZE) (PTRLO + 1) PTRHI; KAlign DATA 16;
    KWr (SA DATA 0) SIZE; KUnk (SA DATA 0) SIZE; KShOk (SA DATA 0) SIZE;
    KDisj (SA DATA 0) SIZE (SA e_sp (- YLO)) (ELit (YLO + WSTK));                (* [comment removed for export] *)
    img_apart DATA 0 SIZE; shmap_apart DATA 0 SIZE ].                           (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stk_facts : list kentry :=
  [ KAlign e_sp 16; KRange e_sp (CEIL + YLO) (two47 - 16); KWr (SA e_sp (- YLO)) (ELit YLO); KRange (EVar 7) 0 SZHI ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ARR_INIT : Z := 0x22b20.
Definition ARR_SH : kentry := KShOk (SA (ELit 0) ARR_INIT) (ELit 24).
Definition static_facts : list kentry := NEWH ++ RTC ++ [KIMGA] ++ GLZ_LOWSH ++ [ARR_SH].
Definition kn_base : list kentry := data_facts ++ stk_facts ++ static_facts.
(* [comment removed for export] *)
Definition kn_in : list kentry :=
  kn_base ++ [ KUnk (SA e_sp (- YLO)) (ELit YLO); KShOk (SA e_sp (- YLO)) (ELit YLO); KRange e_mtr 0 MTRIN; KRange e_fb FBNEED FMIN ].
Definition mkcs (p : Z) (regs : list expr) (k : list kentry) (nx : nat) (vis : list (expr * expr)) (mtr : expr) : acs :=
  ACS (mk_ss p regs k nx) [] 0 YLO 0 vis [] 0 e_sp FdStd false mtr [] e_fb.
Definition tin : acs := mkcs ENTRY regsT kn_in NXF [(DATA, SIZE)] e_mtr.

(* [comment removed for export] *)
Definition xMTR : expr := EVar 33.
Definition XLO : nat := 34.
Definition clobbered : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition regs_out : list expr := sr_havoc (sr_upd regsT 10 (ELit 0)) clobbered XLO.
Definition kn_out : list kentry := kn_base ++ [ KRange (esub xMTR e_mtr) 0 MTRGROW; KRange xMTR 0 GKCAP ].
Definition tout : acs := mkcs RETPC regs_out kn_out (XLO + 14)%nat [(DATA, SIZE)] xMTR.
Definition BCAP : Z := 11 * 2 ^ 30.             (* [comment removed for export] *)
Definition CCAP : Z := 12.                      (* [comment removed for export] *)
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End FuzzN.

Module FuzzE.
Import FuzzN.
Definition DUMMY : Z := 0x640820.               (* [comment removed for export] *)
Definition kn_base : list kentry := [ KRange SIZE 0 0 ] ++ stk_facts ++ static_facts.
Definition kn_in : list kentry :=
  kn_base ++ [ KUnk (SA e_sp (- YLO)) (ELit YLO); KShOk (SA e_sp (- YLO)) (ELit YLO); KRange e_mtr 0 MTRIN; KRange e_fb FBNEED FMIN ].
Definition tin : acs := mkcs ENTRY (sr_upd regsT 10 (ELit DUMMY)) kn_in NXF [] e_mtr.
Definition kn_out : list kentry := kn_base ++ [ KRange (esub xMTR e_mtr) 0 MTRGROW; KRange xMTR 0 GKCAP ].
Definition tout : acs := mkcs RETPC regs_out kn_out (XLO + 14)%nat [] xMTR.
Definition BCAP : Z := 2 ^ 30.
Definition CCAP : Z := 10.
Definition ce : gcallee := GCE NXF tin [tout] BCAP CCAP.
End FuzzE.

(* [comment removed for export] *)
Definition ceN : gcallee := FuzzN.ce.
Definition ceE : gcallee := FuzzE.ce.
End BoFZ.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.AzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.AzImageBoth OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.GlzArith OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesArith OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPopcnt OSSVerify.Proofs.glaze.binary_reflection.lib.AzNodesImg OSSVerify.Proofs.glaze.binary_reflection.lib.AzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.AzCall OSSVerify.Proofs.glaze.binary_reflection.lib.AzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.AzDev OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst BoDrvIT BoDrvNodesP OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.RunLim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BgCommon.    (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import GPS.
Open Scope Z_scope.
(* [comment removed for export] *)
Ltac vmc := first [ match goal with |- @eq ?A ?l ?r => vm_cast_no_check (@eq_refl A r) end | vm_cast_no_check (@eq_refl bool true) ].

(* [comment removed for export] *)
Definition P_MAIN : Z := 0x9d030.
Definition RA_MAIN : Z := 0xed5c4.        (* [comment removed for export] *)
Definition GP : Z := 0x10800.
Definition TP : Z := 0x641380.
Definition FILE1 : Z := 0x10a6b8.         (* [comment removed for export] *)
Definition FILE2 : Z := 0x10a5c8.         (* [comment removed for export] *)
Definition SBUF0 : Z := 0x661a88.         (* [comment removed for export] *)
Definition COMPLETED : Z := 0x10ab50.     (* [comment removed for export] *)
Definition READ_STAGE : Z := 0x630810.    (* [comment removed for export] *)
Definition REG_FLAG : Z := 0x10ab00.      (* [comment removed for export] *)
Definition INIT_BYTE : Z := 0x640810.


Definition NEWH_CELL : Z := 0x640840.
Definition TID_CELL : Z := 0x6412d8.      (* [comment removed for export] *)
Definition ERRNO : Z := 0x6412dc.         (* [comment removed for export] *)
Definition CANARY : Z := 0x6613c0.        (* [comment removed for export] *)
Definition ATEXIT_LO : Z := 0x6613d0.     (* [comment removed for export] *)
Definition ATX_F1 : Z := 0x6613f8.        (* [comment removed for export] *)
Definition ATX_A1 : Z := 0x6614f8.
Definition EXIT_LOCK : Z := 0x6615f0.
Definition RTC_SB : Z := 0x10e1b8.        (* [comment removed for export] *)
Definition RTC_UAR : Z := 0x10e1c0.       (* [comment removed for export] *)
Definition ASAN_INITED : Z := 0x10ee98.
Definition CF_W1 : Z := 0x19fd38.         (* [comment removed for export] *)
Definition CF_W2 : Z := 0x19fde0.         (* [comment removed for export] *)
Definition OFL_HEAD : Z := 0x661a78.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition SP0 : expr := EVar 0.      (* [comment removed for export] *)
Definition ARGC : expr := EVar 1.
Definition D0 : expr := EVar 2.       (* [comment removed for export] *)
Definition L0 : expr := EVar 3.       (* [comment removed for export] *)
Definition D1 : expr := EVar 5.
Definition L1 : expr := EVar 6.
Definition TID : expr := EVar 7.
Definition CAN : expr := EVar 8.
Definition K (i : nat) : expr := EVar (9 + i)%nat.   (* [comment removed for export] *)
Definition G0 : expr := K 17.         (* [comment removed for export] *)
Definition G1 : expr := K 18.         (* [comment removed for export] *)
Definition H0 : expr := K 4.          (* [comment removed for export] *)
Definition H1 : expr := K 5.          (* [comment removed for export] *)
Definition NXD : nat := 9.
Definition NXM : nat := 29.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STR0 : expr := eadd SP0 D0.
Definition STR1 : expr := eadd SP0 D1.
Definition END0 : expr := eadd STR0 L0.     (* [comment removed for export] *)
Definition END1 : expr := eadd STR1 L1.
Definition YLO : Z := 8388608 - 48.
(* [comment removed for export] *)
Definition DRG : Z := EVT + KFREE.
Definition drung (i : nat) (cap mtr : expr) : kentry :=
  KRange (esub (eaddz (escale (2 ^ (13 - Z.of_nat i)) cap) (Z.of_nat i * DRG + EVT)) mtr) 0 (2 ^ 62).
Definition drv_ladder (cap mtr : expr) : list kentry := map (fun i => drung i cap mtr) (seq 0 11).
Definition DMTRHI : Z := 24 * EVT.

(* [comment removed for export] *)
Definition LIMIT : Z := StoreOk.RunLim.LMIN.

(* [comment removed for export] *)
Definition regsM : list expr :=
  [ELit 0; ELit RA_MAIN; SP0; ELit GP; ELit TP;
   K 1; K 2; K 3;
   eaddz SP0 56; ARGC;
   ARGC; eaddz SP0 56; K 16; K 6; K 7; K 8; K 9; K 10;
   ELit P_MAIN; K 16; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0;
   K 12; K 13; K 14; K 15].

(* [comment removed for export] *)
Definition PERM_A : list (expr * expr) :=
  [(ELit FILE1, ELit 232); (ELit FILE2, ELit 232); (ELit SBUF0, ELit 0x408); (ELit COMPLETED, ELit 1);
   (ELit INIT_BYTE, ELit 8); (ELit NEWH_CELL, ELit 8); (ELit ERRNO, ELit 4); (ELit ATEXIT_LO, ELit 24); (ELit EXIT_LOCK, ELit 4);
   (ELit READ_STAGE, ELit 65536); (ELit REG_FLAG, ELit 8); (ELit ATX_F1, ELit 8); (ELit ATX_A1, ELit 8)].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KIMG_A : list kentry :=
  [KImg 0x10000 0x107000; KImg 0x107000 0x107e98; KImg 0x10a568 0x10a8c0; KImg 0x10a8c0 0x10ab00; KImg 0x10ab50 0x10ab58; KImg 0x1a0060 0x1a0061;
   KImg READ_STAGE (READ_STAGE + 65536); KImg 0x640810 0x640848; KImg 0x6613d0 0x6613d8; KImg 0x6613e8 0x6613f0; KImg 0x6615f0 0x6615f4;
   KImg 0x661613 0x661614].
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LOWSH : list kentry :=
  [KZero (SA (ELit 0) 0x7fffa000) (ELit 0x255c); KZero (SA (ELit 0) 0x800194aa) (ELit 0x6e); KZero (SA (ELit 0) 0x800be0f8) (ELit 0x6508)].   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition GLZSH : list kentry :=
  [KZero (SA (ELit 0) (SB + 0x22b80 / 8)) (ELit ((0x26960 - 0x22b80) / 8)); KShOk (SA (ELit 0) 0x22b80) (ELit (0x26960 - 0x22b80));
   KZero (SA (ELit 0) (SB + 0x26ac0 / 8)) (ELit ((0x31340 - 0x26ac0) / 8)); KShOk (SA (ELit 0) 0x26ac0) (ELit (0x31340 - 0x26ac0));   (* [comment removed for export] *)
   KShOk (SA (ELit 0) 0x22b00) (ELit 12);
   KZero (SA (ELit 0) (SB + 0x10000 / 8)) (ELit ((0x22ae0 - 0x10000) / 8)); KShOk (SA (ELit 0) 0x10000) (ELit (0x22ae0 - 0x10000));   (* [comment removed for export] *)
   KShOk (SA (ELit 0) 0x22b20) (ELit 24)].

(* [comment removed for export] *)
Definition RTCELLS : list kentry :=
  [KWord (SA (ELit 0) RTC_SB) 8 (ELit SB); KWord (SA (ELit 0) RTC_UAR) 4 (ELit 1); KWord (SA (ELit 0) ASAN_INITED) 1 (ELit 1);
   KWord (SA (ELit 0) CF_W1) 8 (ELit 0x100000000); KWord (SA (ELit 0) CF_W2) 8 (ELit 0x101010101010101);
   KWord (SA (ELit 0) 0x6613d8) 4 (ELit 1); KWord (SA (ELit 0) 0x6613e0) 8 (ELit 0x6613e8);
   KWord (SA (ELit 0) 0x6613f0) 8 (ELit 0xedc70); KWord (SA (ELit 0) 0x6614f0) 8 (ELit 0x8ca90);
   KWord (SA (ELit 0) OFL_HEAD) 8 (ELit 0);
   (* [comment removed for export] *)
   KUnk (SA (ELit 0) 0x7fffc55c) (ELit 0x800); KUnk (SA (ELit 0) 0x80019518) (ELit 0x48);      (* [comment removed for export] *)
   KWord (SA (ELit 0) REG_FLAG) 8 (ELit 1); KWord (SA (ELit 0) 0x10b9d0) 8 (ELit 0x101010000000001); KWord (SA (ELit 0) 0x19fd60) 8 (ELit 18446744073709551615)].
Definition knM : list kentry :=
  [ KRange SP0 (CEIL + YLO) (HI47 - 48); KAlign SP0 16; KRange TID 1 4194303;
    KRange ARGC 1 1024; KRange D0 240 4194304; KRange L0 0 131071;
    KRange G0 17 4194304; KAlign (eadd END0 G0) 64; KRange (eadd END0 G0) 0 two47;                           (* [comment removed for export] *)
    KWord (SA SP0 48) 8 ARGC; KWord (SA SP0 56) 8 STR0;
    KWord (SA END0 0) 1 (ELit 0); KBlob (SA STR0 0) L0 1;
    KRange H0 1 4194304; KAlign (eadd END0 H0) 8; KRange (eadd END0 H0) 1 two47; KUnk (SA STR0 0) (eadd L0 H0);                               (* [comment removed for export] *)
    KWord (SA (ELit 0) TID_CELL) 4 TID; KWord (SA (ELit 0) CANARY) 8 CAN;
    KWr (SA SP0 (- YLO)) (ELit YLO); KUnk (SA SP0 (- YLO)) (ELit YLO);
    KShOk (SA SP0 (- YLO)) (ELit (YLO + 48));                     (* [comment removed for export] *)
    KShOk (SA SP0 48) (eaddz (eadd (eadd D0 L0) G0) (-48)) ]                        (* [comment removed for export] *)
  ++ map (fun w => KWr (SA (fst w) 0) (snd w)) PERM_A
  ++ RTCELLS ++ LOWSH ++ GLZSH ++ KIMG_A.
(* [comment removed for export] *)
Definition mkM (p : Z) (regs : list expr) (k : list kentry) : acs :=
  ACS (mk_ss p regs k NXM) [] 0 YLO 0 [] PERM_A 0 (eaddz SP0 0) FdStd false (ELit 0) [] (ELit FMIN).   (* [comment removed for export] *)
Definition tMA : acs := mkM P_MAIN regsM knM.
(* [comment removed for export] *)
Definition tMu1 : acs := add_kn tMA [KRange ARGC 1 1].
Definition tMu3 : acs := add_kn tMA [KRange ARGC 3 1024].
(* [comment removed for export] *)
Definition knO : list kentry :=
  [KRange ARGC 2 2; KRange D1 241 4194304; KRange L1 0 131071; KWord (SA SP0 64) 8 STR1; KWord (SA END1 0) 1 (ELit 0); KBlob (SA STR1 0) L1 2;
   KRange H1 1 4194304; KAlign (eadd END1 H1) 8; KRange (eadd END1 H1) 1 two47; KUnk (SA STR1 0) (eadd L1 H1); KShOk (SA SP0 48) (eaddz (eadd (eadd D1 L1) G1) (-48));
   KRange G1 17 4194304; KAlign (eadd END1 G1) 64; KRange (eadd END1 G1) 0 two47].
Definition tMo : acs := add_kn tMA knO.

(* [comment removed for export] *)
Definition CT0 (id : nat) : option gcallee := None.
Definition BCAP : Z := GBUDGET.      (* [comment removed for export] *)
Definition CCAP : Z := GCOUNT.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition meter_fix (old : expr) (cs' : acs) : acs :=
  let k := kn cs' in let new := a_meter cs' in
  match xlo k old, xhi k old, xlo k (esub new old), xhi k (esub new old) with
  | Some ol, Some oh, Some dl, Some dh =>
      if (Z.leb 0 ol && Z.leb 0 dl && Z.ltb (oh + dh) two64)%bool then add_kn cs' [KRange new (ol + dl) (oh + dh)] else cs'
  | _, _, _, _ => cs'
  end.
(* [comment removed for export] *)
Fixpoint kn_undup (seen l : list kentry) : list kentry :=
  match l with
  | [] => []
  | K :: r => if existsb (kentry_eqb K) seen then kn_undup seen r else K :: kn_undup (K :: seen) r
  end.
Definition kn_dedup (cs : acs) : acs := set_kn cs (kn_undup [] (kn cs)).
Definition FZN (cs : acs) : option acs :=
  option_map (fun c => kn_dedup (meter_fix (a_meter cs) c)) (node_call BSEGS ABOTH NXD BCAP CCAP GBOTH BoFZ.ceN [ELit 0; a_meter cs; a_fbud cs] cs).
Definition FZE (cs : acs) : option acs :=
  option_map (fun c => kn_dedup (meter_fix (a_meter cs) c)) (node_call BSEGS ABOTH NXD BCAP CCAP GBOTH BoFZ.ceE [ELit 0; ELit 0; a_meter cs; a_fbud cs] cs).
Definition XNa (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 120 then FZN cs else if Nat.eqb id 121 then FZE cs
  else DNA.XNP BSEGS NXD GBOTH (XNc BSEGS ITA ABOTH NXD GBOTH BCAP CCAP CT0) id args cs.
Definition XEa := DNA.XEP BSEGS NXD.
Definition HS0 (h : nat) : option acs := None.
Definition FUEL : nat := 400.
Definition BF : nat := 3000.
(* [comment removed for export] *)
Definition XAnone (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.
Definition XAa (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := DNA.XAP BSEGS NXD XAnone id args cs.
Definition M12 (cs : acs) : option (acs * acs) := XAg BSEGS NXD GBOTH BCAP CCAP 12%nat [] cs.
(* [comment removed for export] *)
Definition FUEL0 : nat := 400.
Definition BF0 : nat := 3000.
Definition CHK0 (cs : acs) (p : plan) : cres :=
  checkA BSEGS ITA ABOTH NXD LIMIT ISP0 XNa XEa XB0 XAa AP.XT0 (fun _ => None) 0%nat false BF0 FUEL0 None cs p.
Definition SU0 : list Z := [DNA.X_STDIO_WRITE; DNA.X_MODULE_DTOR].
Definition tailF : plan := PRun SU0 (PEmit 64 [] (PRun SU0 PExit)).
Definition tailN : plan := PRun SU0 PExit.
(* [comment removed for export] *)
Definition XT70g (chk0 : acs -> plan -> cres) (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * Z) :=
  if negb (Nat.eqb id 70) then None else
  match DNA.node_module_dtor BSEGS NXD cs with
  | Some cs1 =>
      match chk0 cs1 tailF with
      | COk (SEmitP fd ps (SExit c)) => Some (fd, ps, c)
      | _ => match chk0 cs1 tailN with COk (SExit c) => Some (1, [], c) | _ => None end
      end
  | None => None
  end.
Definition XT70 : nat -> list expr -> acs -> option (Z * list spiece * Z) := XT70g CHK0.
Definition XTa : nat -> list expr -> acs -> option (Z * list spiece * Z) := XT70.
Definition CHKa (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  checkA BSEGS ITA ABOTH NXD LIMIT ISP0 XNa XEa XB0 XAa XTa hs 0%nat false bf fuel None cs p.
(* [comment removed for export] *)
Definition XNz (id : nat) (args : list expr) (cs : acs) : option acs :=
  if (Nat.eqb id 20 || Nat.eqb id 120 || Nat.eqb id 121)%bool then None else XNa id args cs.
Definition CHK0z (cs : acs) (p : plan) : cres :=
  checkA BSEGS ITA ABOTH NXD LIMIT ISP0 XNz XEa XB0 XAa AP.XT0 (fun _ => None) 0%nat false BF0 FUEL0 None cs p.
Definition XTz : nat -> list expr -> acs -> option (Z * list spiece * Z) := XT70g CHK0z.
Definition CHKz (hs : nat -> option acs) (bf fuel : nat) (cs : acs) (p : plan) : cres :=
  checkA BSEGS ITA ABOTH NXD LIMIT ISP0 XNz XEa XB0 XAa XTz hs 0%nat false bf fuel None cs p.



(* [comment removed for export] *)
Definition hole_of (d : acs) (r : cres) : acs := match r with CErr _ _ cs => cs | COk _ => d end.
Definition HSof1 (h : acs) (i : nat) : option acs := match i with 1%nat => Some h | _ => None end.
(* [comment removed for export] *)
Definition SU : list Z :=
  [DNA.X_ISTRLEN; DNA.X_REGION; DNA.X_STDIO_WRITE; DNA.X_MEMCHR; DNA.X_MODULE_DTOR; g_memcpy GBOTH; g_memset GBOTH;
   fst (fst (fst (fst DNA.QC_PRINTF))); fst (fst (fst (fst DNA.QC_STRNLEN))); fst (fst (fst (fst DNA.QC_MEMCHR)));
   g_malloc_thunk GBOTH; g_free_thunk GBOTH; DNA.X_FUZZ].
Definition R (k : plan) : plan := PRun SU k.
Definition X (id : nat) (k : plan) : plan := PRun SU (PExt id [] k).
Definition W (k : plan) : plan := PRun SU (PEmit 64 [] k).
(* [comment removed for export] *)
Definition pEXIT : plan := PRun SU (PTerm 70 []).   (* [comment removed for export] *)
