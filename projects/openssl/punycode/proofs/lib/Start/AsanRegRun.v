(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanNodesLib.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanDescs AsanRehash AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module RGN.
Import RGM.

(* [comment removed for export] *)
Definition NRG : nat := 19.

(* [comment removed for export] *)
#[local] Notation znodup := RHN.znodup (only parsing).
#[local] Notation lit1 := RHN.lit1 (only parsing).
#[local] Notation key_facts := RHN.key_facts (only parsing).

(* [comment removed for export] *)
#[local] Notation collect := RHN.collect (only parsing).
#[local] Notation keys_of := RHN.keys_of (only parsing).
#[local] Notation havs := RHN.havs (only parsing).

(* [comment removed for export] *)
Fixpoint zins (x : Z) (l : list Z) : list Z := match l with [] => [x] | h :: r => if Z.leb x h then x :: l else h :: zins x r end.
Fixpoint zsort (l : list Z) : list Z := match l with [] => [] | x :: r => zins x (zsort r) end.
(* [comment removed for export] *)
Fixpoint split_at (a b : Z) (l : list Z) : list (Z * Z) :=
  match l with
  | [] => if Z.ltb a b then [(a, b)] else []
  | o :: r => if Z.ltb o a then split_at a b r
              else if Z.leb b o then (if Z.ltb a b then [(a, b)] else [])
              else (if Z.ltb a o then [(a, o)] else []) ++ split_at (o + 1) b r
  end.
(* [comment removed for export] *)
Definition gaps_of (k : list kentry) (l : list Z) (hlo hhi : Z) : list (Z * Z) :=
  flat_map (fun K => match K with
                     | KImg lo hi => if (Z.ltb lo hhi && Z.ltb hlo hi)%bool then split_at (Z.max lo hlo) (Z.min hi hhi) l else []
                     | _ => []
                     end) k.
(* [comment removed for export] *)
Definition gap_ok (k : list kentry) (os : list Z) (wlo whi : Z) (g : Z * Z) : bool :=
  (Z.ltb (fst g) (snd g) && Z.leb wlo (fst g) && Z.leb (snd g) whi && img_cov k (fst g) (snd g)
   && forallb (fun o => Z.ltb o (fst g) || Z.leb (snd g) o) os)%bool.
Definition good_gaps (k : list kentry) (os : list Z) (wlo whi hlo hhi : Z) : list (Z * Z) :=
  List.filter (gap_ok k os wlo whi) (gaps_of k (zsort os) hlo hhi).
Definition gap_facts (k : list kentry) (os : list Z) (wlo whi hlo hhi : Z) : list kentry :=
  map (fun g => KImg (fst g) (snd g)) (good_gaps k os wlo whi hlo hhi).

Section Node.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable T : ctab.
#[local] Notation y := (c_lay T) (only parsing).

(* [comment removed for export] *)
Fixpoint scan (n : nat) (a : Z) : option (list desc) :=
  match n with
  | O => Some []
  | S n' => match DSC.rd64 segs a, DSC.rd64 segs (a + 8), DSC.rd64 segs (a + 16), DSC.rd64 segs (a + 40), DSC.rd64 segs (a + 56), scan n' (a + 64) with
            | Some b, Some sz, Some w, Some dy, Some od, Some r => Some (D b sz w dy od :: r)
            | _, _, _, _, _, _ => None
            end
  end.

#[local] Notation ro_cov := (RHN.ro_cov segs) (only parsing).

(* [comment removed for export] *)
Definition cell_is (k : list kentry) (a : Z) (w : nat) (v : Z) : bool :=
  match kreadZ segs k (ELit 0) a w with Some z => Z.eqb z v | None => false end.

(* [comment removed for export] *)
Definition read_map (k : list kentry) : option (expr * Z * Z * list Z) :=
  match kread8e segs k (ELit 0) (c_map T), kreadZ segs k (ELit 0) (c_map T + 8) 4, kreadZ segs k (ELit 0) (c_map T + 16) 4 with
  | Some B, Some ne, Some N =>
      let '(nb, no) := split_lit B in
      match keys_of (collect k nb) no (Z.to_nat N) with
      | Some ks => Some (B, N, ne, ks)
      | None => None
      end
  | _, _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition chk_regs (cs : acs) : bool :=
  match lit1 (reg cs 9), lit1 (reg cs 20), lit1 (reg cs 21), lit1 (reg cs 24), lit1 (reg cs 25) with
  | Some r9, Some r20, Some r21, Some r24, Some r25 =>
      (Z.eqb r9 (c_tab T) && Z.eqb r20 (c_shcell T) && Z.eqb r21 1 && Z.eqb r24 (c_flags T) && Z.eqb r25 (c_statics T))%bool
  | _, _, _, _, _ => false
  end.

(* [comment removed for export] *)
Definition chk_tab (k : list kentry) (i kz n : Z) (ds : list desc) : bool :=
  (Z.leb 1 kz && Z.leb kz (2 ^ 20) && Z.eqb (Z.of_nat (length ds)) kz && Z.leb 0 i && Z.ltb (i + kz) n && Z.leb (c_tab T + 64 * n) (c_tabend T)
   && img_cov k (c_tab T + 64 * i) (c_tab T + 64 * (i + kz)) && Z.leb 0 (c_tab T) && Z.ltb (c_tab T + 64 * n) (2 ^ 40)
   && znodup (inds ds) && forallb (fun o => cell_is k o 1 0) (inds ds)
   && kwritable_x k k (ELit 0) (l_odr_lo y) (ELit (l_odr_hi y - l_odr_lo y))
   && Z.leb (img_lo A) (l_odr_lo y) && Z.leb (l_odr_hi y) (img_hi A) && Z.leb 0 (l_odr_lo y) && Z.ltb (l_odr_lo y) (l_odr_hi y))%bool.

(* [comment removed for export] *)
Definition chk_consts (k : list kentry) : bool :=
  (cell_is k (c_inited T) 1 1 && kwritable_x k k (ELit 0) (c_inited T) (ELit 1)
   && cell_is k (c_flags T + 24) 4 1 && cell_is k (c_flags T + 85) 1 1 && cell_is k (c_flags T + 100) 4 2
   && cell_is k (c_shcell T) 8 (l_shb y) && cell_is k (c_canpoison T) 1 1 && cell_is k (c_msetcell T) 8 (c_memset T)
   && cell_is k (c_llaalign T) 8 8
   && forallb (fun a => Z.leb (img_lo A) a && Z.leb (a + 128) (img_hi A))
        [c_inited T; c_flags T; c_shcell T; c_canpoison T; c_msetcell T; c_llaalign T; c_lla T; c_statics T; c_map T])%bool.

(* [comment removed for export] *)
Definition chk_frame (k : list kentry) (fp sp ek es : expr) (kb : expr) (ko : Z) (n : Z) : bool :=
  match kreadZ segs k kb (ko - 8) 8, kreadZ segs k kb (ko - 0x28) 8, xlo k (esub fp sp), xhi k (esub fp sp), xlo k sp, xhi k fp, xlo k fp with
  | Some n', Some p, Some dlo, Some dhi, Some splo, Some fphi, Some fplo =>
      (Z.eqb n' n && Z.eqb p (c_msetcell T) && Z.eqb dlo 0x10f0 && Z.eqb dhi 0x10f0 && Z.leb 0x10f0 fplo && Z.leb 4 (ealign k fp)
       && Z.leb (l_ihi y + 32) splo && Z.leb (shad y (l_ihi y) + 32) splo && Z.ltb fphi (2 ^ 47)
       && LBN.ovl_ok A k ek (ELit 8) && LBN.ovl_ok A k es (ELit 32) && Z.leb 0 (l_ihi y))%bool
  | _, _, _, _, _, _, _ => false
  end.

(* [comment removed for export] *)
Definition chk_shadow (k : list kentry) (ds : list desc) : bool :=
  let wlo := shad y (l_ilo y) in let whi := shad y (l_ihi y) in
  (LBN.ovl_ok A k (ELit wlo) (ELit (whi - wlo)) && Z.leb wlo (run_sh_lo y ds) && Z.leb (run_sh_lo y ds) (run_sh_hi y ds)
   && Z.leb (run_sh_hi y ds) whi && Z.leb (img_hi A) wlo && Z.ltb wlo whi && Z.ltb whi (2 ^ 47)
   && Z.eqb (l_ilo y) (img_lo A) && Z.eqb (l_ihi y) (img_hi A))%bool.

(* [comment removed for export] *)
Definition chk_lla (k : list kentry) (cur lend : expr) (cb : expr) (co : Z) (sb : expr) (so : Z) (na : Z) : bool :=
  match xlo k cur, xhi k lend, xlo k (esub lend cur), xhi k (esub lend cur), xhi k cur with
  | Some curlo, Some lendhi, Some roomlo, Some roomhi, Some curhi =>
      (Z.ltb 0 curlo && Z.leb (16 * na) roomlo && Z.leb roomhi (2 ^ 47) && Z.ltb curhi (2 ^ 47) && Z.ltb lendhi (2 ^ 47)
       && LBN.ovl_ok A k cur (ELit (16 * na))
       && kwritable_x k k (ELit 0) (c_lla T) (ELit 16)
       && ranges_apart_x k cb co (ELit (16 * na)) (ELit 0) (shad y (l_ilo y)) (ELit (shad y (l_ihi y) - shad y (l_ilo y)))
       && ranges_apart_x k cb co (ELit (16 * na)) sb so (ELit (0x10f0 + 32))
       && (Z.leb (c_lla T + 16) (l_odr_lo y) || Z.leb (l_odr_hi y) (c_lla T + 8)))%bool
  | _, _, _, _, _ => false
  end.

(* [comment removed for export] *)
Definition chk_list (k : list kentry) (size kz : Z) : bool :=
  (Z.leb 1 size && Z.ltb (size + kz) (2 ^ 62) && kwritable_x k k (ELit 0) (c_statics T + 8) (ELit 16)
   && (Z.leb (c_statics T + 24) (l_odr_lo y) || Z.leb (l_odr_hi y) (c_statics T + 8)))%bool.

(* [comment removed for export] *)
Definition chk_map (cs : acs) (k : list kentry) (B : expr) (N ne : Z) (ks : list Z) (nb : expr) (no : Z) (cb : expr) (co : Z) (sb : expr) (so : Z) (na : Z) : bool :=
  (cell_is k (c_statics T + 56) 8 (c_map T) && kwritable_x k k (ELit 0) (c_statics T + 56) (ELit 8)
   && cell_is k (c_map T + 12) 4 0 && kwritable_x k k (ELit 0) (c_map T) (ELit 20)
   && Z.leb 8 N && Z.leb N (2 ^ 20) && Z.leb 0 ne && forallb (fun key => Z.leb 0 key && Z.ltb key (2 ^ 64)) ks
   && AP.expr_vars_lt (nxt cs) B
   && match xlo k B, xhi k B with Some blo, Some bhi => Z.ltb 0 blo && Z.leb (bhi + 32 * N) (2 ^ 47) | _, _ => false end
   && Z.leb 3 (ealign k B) && LBN.ovl_ok A k B (ELit (32 * N))
   && ranges_apart_x k nb no (ELit (32 * N)) (ELit 0) (shad y (l_ilo y)) (ELit (shad y (l_ihi y) - shad y (l_ilo y)))
   && ranges_apart_x k nb no (ELit (32 * N)) cb co (ELit (16 * na))
   && ranges_apart_x k nb no (ELit (32 * N)) sb so (ELit (0x10f0 + 32))
   && (Z.leb (c_map T + 12) (l_odr_lo y) || Z.leb (l_odr_hi y) (c_map T + 8)))%bool.

Definition node_regrun (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  match args with
  | [ELit kz] =>
    if negb (Z.eqb (pc cs) (c_entry T)) then None else
    let fp := reg cs 8 in let sp := reg cs 2 in
    let ek := eaddz fp (-0x10a8) in let '(kb, ko) := split_lit ek in
    let es := eaddz sp (-32) in let '(sb, so) := split_lit es in
    match lit1 (reg cs 27), kreadZ segs k kb (ko - 8) 8 with
    | Some i, Some n =>
      match scan (Z.to_nat kz) (c_tab T + 64 * i), kread8e segs k (ELit 0) (c_lla T), kread8e segs k (ELit 0) (c_lla T + 8),
            kreadZ segs k (ELit 0) (c_statics T + 8) 8, kread8e segs k (ELit 0) (c_statics T + 16) with
      | Some ds, Some lend, Some cur, Some size, Some first =>
        let nin := nind ds in let na := kz + nin in
        let hasmap := Z.ltb 0 nin in
        match (if hasmap then read_map k else Some (ELit 0, 0, 0, [])) with
        | Some (B, N, ne, ks) =>
          match run y N ds ks ne with
          | Some (ks', ne') =>
            let '(cb, co) := split_lit cur in let '(nb, no) := split_lit B in
            let shlo := run_sh_lo y ds in let shhi := run_sh_hi y ds in
            if (fresh_ok nx0 cs && ro_cov k && AP.expr_vars_lt (nxt cs) cur && chk_regs cs && chk_tab k i kz n ds && chk_consts k
                && chk_frame k fp sp ek es kb ko n && chk_shadow k ds && chk_lla k cur lend cb co sb so na && chk_list k size kz
                && (negb hasmap || chk_map cs k B N ne ks nb no cb co sb so na))%bool
            then
              let nx := nxt cs in
              let sr' := sr_upd (sr_fresh (s_regs (a_ss cs)) rg_fresh nx) 27 (ELit (i + kz)) in
              let kh := havs k ([(kb, ko, 8); (sb, so, 32); (ELit 0, shlo, shhi - shlo);
                                 (ELit 0, c_statics T + 8, 16); (ELit 0, c_lla T + 8, 8); (cb, co, 16 * na)]
                                ++ (if hasmap then [(ELit 0, ind_lo ds, ind_hi ds - ind_lo ds); (ELit 0, c_map T + 8, 4); (nb, no, 32 * N)] else [])) in
              let k' := KWord (SA (ELit 0) (c_lla T + 8)) 8 (eaddz cur (16 * na))
                        :: KWord (SA (ELit 0) (c_statics T + 8)) 8 (ELit (size + kz))
                        :: KWord (SA (ELit 0) (c_statics T + 16)) 8 (eaddz cur (16 * na - 16))
                        :: (if hasmap then KWord (SA (ELit 0) (c_map T + 8)) 4 (ELit ne') :: key_facts nb no ks' else [])
                        ++ gap_facts k (inds ds) (l_odr_lo y) (l_odr_hi y) (ind_lo ds) (ind_hi ds) ++ kh in
              Some (with_ss cs (mk_ss (c_entry T) sr' k' (nx + NRG)))
            else None
          | None => None
          end
        | None => None
        end
      | _, _, _, _, _ => None
      end
    | _, _ => None
    end
  | _ => None
  end.

End Node.
End RGN.
