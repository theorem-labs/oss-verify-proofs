From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymFrame SymEntail SymCFG SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVx.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L5 Require Import S_hf hf_defs hf_cuts hf_tail hf_tailc hf_pc.
Require OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_defs.
Import OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Lib_handle__G1.Lib_handle_f_nodes.
Import HfAddrU.
Import ListNotations.
Open Scope Z_scope.

(* Token region of ubsan handle_f: states at the token-scan latch (pc_tok_U), at the corner vr call, and after
   the call.  Cursor pQ (current char), token start pT0, cursor after the token pC. *)

(* Token-scan latch.  r11 is written (xB + 1) + pQ so that infer_sub binds pQ by offset from the leaf value. *)
Definition rQ1 : sv := SAlu ALU_ADD (SAlu ALU_ADD xB (SLit 1)) pQ.
Definition tokLregs (cnt cm2 : sv) : list (nat * sv) :=
  [(10%nat, txt xE0); (11%nat, rQ1); (18%nat, xb 720); (19%nat, SLit 2); (20%nat, txt pQ); (22%nat, SLit 32);
   (23%nat, SLit 9); (24%nat, cnt); (25%nat, cm2); (26%nat, txt pT0); (27%nat, magic_U)].
Definition tokF : list sprop := [SPUle xP0 pT0; SPUle pT0 pQ; SPUlt pQ xE0].
Definition T94z_U : sstate :=
  HS_U pc_tok_U (tokLregs (SLit 0) (SLit (-2))) [] pQ (t_d co1, SLit 0, t_k co1) [] tokF.
Definition T94n_U : sstate :=
  HS_U pc_tok_U (tokLregs pA am2) [] pQ coA [] (tokF ++ [SPUle pA (SLit (2 ^ 20))] ++ nzA_U).
Definition vT94_U : sv := VT pQ 0.

(* Corner vr call (corners push).  Two exit shapes: after a tab/space the token end r20 = xB + pC (the cursor
   cell); on the end-of-line path r20 = xB + xE0 while the cell holds xB + pC.  The fail posts are computed from
   the shape with r20 a fresh variable (r20 is restored from the frame on the return path). *)
Definition leafT (S : sstate) (pc : Z) : sstate :=
  match sym_run segsU FUEL_U [vrU_entry; pcU_entry; pgU_entry; pc_ws_U; pc_tok_U; pc_while_U; pc_raw_U; pc_tri_U]
          S true with
  | Some ls => nth 0 (filter (fun st => Z.eqb (ss_pc st) pc) (map lf_state ls)) S
  | None => S
  end.
Definition ra_vr_tok : sv := Eval vm_compute in reg_sv (leafT T94z_U vrU_entry) 1.
Definition r20E : sv := SVar 345.
Definition tokEregs (cnt cm2 a1 r20 : sv) : list (nat * sv) :=
  [(1%nat, ra_vr_tok); (10%nat, xb 720); (11%nat, a1); (12%nat, SVar 104); (18%nat, xb 720); (19%nat, SLit 2);
   (20%nat, r20); (22%nat, SLit 32); (23%nat, SLit 9); (24%nat, cnt); (25%nat, cm2); (26%nat, txt pT0);
   (27%nat, magic_U)].
Definition tokEF : list sprop := [SPUle xP0 pT0; SPUlt pT0 pC; SPUle pC xE0].
Definition Evz (r20 : sv) : sstate :=
  HS_U vrU_entry (tokEregs (SLit 0) (SLit (-2)) (SLit 1) r20) [] pC (t_d co1, SLit 0, t_k co1) [] tokEF.
Definition Evn (r20 : sv) : sstate :=
  HS_U vrU_entry (tokEregs pA am2 (SAlu ALU_ADD pA (SLit 1)) r20) [] pC coA []
    (tokEF ++ [SPUle pA (SLit (2 ^ 20)); SPUlt pA (SLit (2 ^ 20))] ++ nzA_U).
Definition Evzm_U : sstate := Evz (txt pC).
Definition Evnm_U : sstate := Evn (txt pC).
Definition Evze_U : sstate := Evz (txt xE0).
Definition Evne_U : sstate := Evn (txt xE0).
Definition vEv_U : sv := VT pC 5.

Definition coz : sv * sv * sv := (t_d co1, SLit 0, t_k co1).
Definition E2zm_U : sstate := Eval vm_compute in E2_of xs_t1 1 Evzm_U.
Definition E2nm_U : sstate := Eval vm_compute in E2_of xs_t1 1 Evnm_U.
Definition E2ze_U : sstate := Eval vm_compute in E2_of xs_t1 1 Evze_U.
Definition E2ne_U : sstate := Eval vm_compute in E2_of xs_t1 1 Evne_U.
Definition szm_U : wsub := Eval vm_compute in s_site E2zm_U coz 12.
Definition snm_U : wsub := Eval vm_compute in s_site E2nm_U coA 12.
Definition sze_U : wsub := Eval vm_compute in s_site E2ze_U coz 12.
Definition sne_U : wsub := Eval vm_compute in s_site E2ne_U coA 12.
Definition nzco_U := Eval vm_compute in nz_site co1 12.
Definition E2zf_U : sstate := Eval vm_compute in E2_of xs_t1 1 (Evz r20E).
Definition E2nf_U : sstate := Eval vm_compute in E2_of xs_t1 1 (Evn r20E).

(* After the call.  TAm_U / TAe_U: keep posts of Evnm_U / Evne_U with the old-count fact 1 <= pA weakened to
   0 <= pA (same list position), so the keep posts of Evzm_U / Evze_U (pA = 0) also entail them. *)
Definition weak1 (S : sstate) : sstate :=
  mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S)
    (map (fun f => if sprop_eqb f (SPUle (SLit 1) pA) then SPUle (SLit 0) pA else f) (ss_facts S))
    (ss_next S) (ss_lenient S).
Definition TAm_U : sstate := Eval vm_compute in weak1 (post_of E2nm_U snm_U nzco_U true).
Definition TAe_U : sstate := Eval vm_compute in weak1 (post_of E2ne_U sne_U nzco_U true).
Definition FAz_U : sstate := Eval vm_compute in post_of E2zf_U (s_site E2zf_U coz 12) nzco_U false.
Definition FAn_U : sstate := Eval vm_compute in post_of E2nf_U (s_site E2nf_U coA 12) nzco_U false.
Definition vTA_U : sv := VT pC 4.

(* parse_corner call after the push.  EPm_U / EPe_U: the pc-entry leaves of TAm_U / TAe_U.  The slot is object 5
   after xs1pc (pc frame split off the dead window, corners data split at the slot); after the call the slot is
   object 2 of the post; xs2pc restores the pre-call object order and merges the pieces back. *)
Definition EPm_U : sstate := Eval vm_compute in leafT TAm_U pcU_entry.
Definition EPe_U : sstate := Eval vm_compute in leafT TAe_U pcU_entry.
Definition xs1pc : list xform := [XSplit 0 (SLit (-64)); XSplit 4 PA.off12A; XSplit 5 PA.off12A12].
Definition obj_same (a b : sobj) : bool :=
  sv_eqb (ob_base a) (ob_base b) && sv_eqb (ob_lo a) (ob_lo b) && sv_eqb (ob_hi a) (ob_hi b).
Fixpoint find_same (o : sobj) (l : list sobj) (n : nat) : nat :=
  match l with [] => 0%nat | x :: r => if obj_same o x then n else find_same o r (S n) end.
Definition pc_parts (E : sstate) : option (sstate * sstate) :=
  match apply_xforms E xs1pc with
  | Some S1 =>
      let E2 := reshape_obj_at S1 5 PA.slot_obj in
      let s := infer_sub 10 E2 PCU.Pre_pc_U in
      match entails_fr E2 PCU.Pre_pc_U s with
      | Some R => Some (S1, reshape_obj_at (pc_post E2 s R (mkLeaf PCU.P_ret_U RsSymJump)) 2 PA.mid_obj)
      | None => None
      end
  | None => None
  end.
Definition sel_of (E : sstate) : list nat :=
  match pc_parts E with Some (S1, C) => map (fun o => find_same o (ss_objs C) 0) (ss_objs S1) | None => [] end.
Definition xs2pc (sel : list nat) : list xform := [XSelect sel; XMerge 4; XMerge 4; XMerge 0].
Definition TP_of (E : sstate) (sel : list nat) : sstate :=
  match pc_parts E with Some (_, C) => optS (apply_xforms C (xs2pc sel)) | None => E end.
Definition selPm : list nat := Eval vm_compute in sel_of EPm_U.
Definition selPe : list nat := Eval vm_compute in sel_of EPe_U.
Definition TPm_U : sstate := Eval vm_compute in TP_of EPm_U selPm.
Definition TPe_U : sstate := Eval vm_compute in TP_of EPe_U selPe.
Definition vEP_U : sv := VT pC 3.
Definition vTP_U : sv := VT pC 2.
