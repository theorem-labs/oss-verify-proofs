From Stdlib Require Import ZArith NArith List Bool PArith.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo lo_defs.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* Measures of a handler call node (E) and of its return nodes (T), P's convention. *)
Module LoMeas.
  Definition rE : Z := 500.
  Definition rT : Z := 500.
  (* Per-site measures (VLp index): call node kE_x, its return nodes kT_x = kE_x - 1; longest path to the loop latch. *)
  Definition kE_se1 : Z := 26.  Definition kT_se1 : Z := 25.
  Definition kE_sdA1 : Z := 23.  Definition kT_sdA1 : Z := 22.
  Definition kE_sdA2 : Z := 21.  Definition kT_sdA2 : Z := 20.
  Definition kE_se2 : Z := 20.  Definition kT_se2 : Z := 19.
  Definition kE_sdA3 : Z := 19.  Definition kT_sdA3 : Z := 18.
  Definition kE_se3 : Z := 18.  Definition kT_se3 : Z := 17.
  Definition kE_sdA4 : Z := 17.  Definition kT_sdA4 : Z := 16.
  Definition kE_se4 : Z := 16.  Definition kT_se4 : Z := 15.
  Definition kE_sdA5 : Z := 15.  Definition kT_sdA5 : Z := 14.
  Definition kE_se5 : Z := 14.  Definition kT_se5 : Z := 13.
  Definition kE_sdA6 : Z := 13.  Definition kT_sdA6 : Z := 12.
  Definition kE_se6 : Z := 12.  Definition kT_se6 : Z := 11.
  Definition kE_sdA7 : Z := 11.  Definition kT_sdA7 : Z := 10.
  Definition kE_sdB1 : Z := 11.  Definition kT_sdB1 : Z := 10.
  Definition kE_da : Z := 10.  Definition kT_da : Z := 9.
  Definition kE_se8 : Z := 10.  Definition kT_se8 : Z := 9.
  Definition kE_sdA8 : Z := 9.  Definition kT_sdA8 : Z := 8.
  Definition kE_sdB2 : Z := 9.  Definition kT_sdB2 : Z := 8.
  Definition kE_vrA : Z := 7.  Definition kT_vrA : Z := 6.
  Definition kE_vrB : Z := 7.  Definition kT_vrB : Z := 6.
  Definition kE_mf : Z := 6.  Definition kT_mf : Z := 5.
  Definition kE_nt : Z := 6.  Definition kT_nt : Z := 5.
  Definition kE_ir : Z := 4.  Definition kT_ir : Z := 3.
  Definition kE_bw : Z := 4.  Definition kT_bw : Z := 3.
  Definition kE_se7 : Z := 4.  Definition kT_se7 : Z := 3.
  Definition kE_se9 : Z := 4.  Definition kT_se9 : Z := 3.
  Definition kE_sdB3 : Z := 4.  Definition kT_sdB3 : Z := 3.
  Definition kE_op1 : Z := 4.  Definition kT_op1 : Z := 3.
  Definition kE_hvn : Z := 2.  Definition kT_hvn : Z := 1.
  Definition kE_hl : Z := 2.  Definition kT_hl : Z := 1.
  Definition kE_hp : Z := 2.  Definition kT_hp : Z := 1.
  Definition kE_hf : Z := 2.  Definition kT_hf : Z := 1.
  Definition kE_ml : Z := 2.  Definition kT_ml : Z := 1.
  Definition kE_fs : Z := 2.  Definition kT_fs : Z := 1.
  Definition kE_si : Z := 2.  Definition kT_si : Z := 1.
  Definition kE_op3 : Z := 2.  Definition kT_op3 : Z := 1.
  Definition kE_op3b : Z := 2.  Definition kT_op3b : Z := 1.
  Definition kE_bwda : Z := 2.  Definition kT_bwda : Z := 1.
End LoMeas.

(* Call-site states until U/L1/lo_sites.v provides the engine leaves: the loop-iteration form of P's E_h,
   at the callee entry with ra = call pc + 4. *)
Module LoSite.
  Definition ifacts : list sprop :=
    [SPUle (SLit 4096) LD.xLD; SPUlt LD.pI LD.xLC; SPUle LD.pE LD.vL; SPUle LD.pLEN (SLit (2 ^ 24)); SPUle LD.pPOS (SLit (2 ^ 26))].
  Definition cfacts : list sprop := [SPUle LD.pCP LD.pE; SPUle LD.pCP (SLit (2 ^ 26))].
  (* s1 = line index + 1 (written once, at 0x13f04) is live at every return: the latch moves it into K_loop's pI. *)
  Definition rI : nat * sv := (9%nat, SAlu ALU_ADD LD.pI (SLit 1)).
  (* At a callee entry t0, t1 and a1 are whatever the caller left there (LS fixes the loop's values 35, 1, vB):
     generic register variables unless the site passes an argument in them. *)
  Definition clob : list (nat * sv) := [(5%nat, LD.hx 5); (6%nat, LD.hx 6); (11%nat, LD.hx 11)].
  Definition sitel (entry ra : Z) (regs : list (nat * sv)) (cp ce loc : list cell) (facts : list sprop) : sstate :=
    LoU.LS entry (clob ++ (1%nat, SLit ra) :: rI :: regs) (Some LD.pLINE) cp ce loc (facts ++ ifacts).
  Definition site (entry ra : Z) (regs : list (nat * sv)) (cp ce : list cell) (facts : list sprop) : sstate :=
    sitel entry ra regs cp ce [] facts.
  (* builder + cursor handlers *)
  Definition hsite (entry ra : Z) : sstate :=
    site entry ra [(10%nat, LoU.bx); (11%nat, LoU.cx)] (LoU.cpC LD.pCP) (LoU.ceC LD.pE) cfacts.
  Definition E_mf : sstate := site 0x18d80 0x14960 [(10%nat, LoU.bx)] [] [] [].
  Definition E_hvn : sstate := hsite 0x1914c 0x142e0.
  Definition E_hl : sstate := hsite 0x19f68 0x14368.
  Definition E_hp : sstate := hsite 0x1a298 0x14390.
  Definition E_hf : sstate := hsite 0x19308 0x143a0.
  Definition E_ir : sstate :=
    site 0x18c6c 0x143ec [(10%nat, LoU.bx); (11%nat, LoU.cx)] (LoU.cpC LD.pCP) (LoU.ceC LD.pE) (SPUle (SLit 1) LD.pE :: cfacts).
  Definition E_ml : sstate := hsite 0x1a6b4 0x14848.
  (* slice_eq: token start / length from next_token *)
  Definition tfacts : list sprop :=
    [SPUle LD.pST LD.vL; SPUle LD.pSL LD.vL; SPUle (SAlu ALU_ADD LD.pST LD.pSL) LD.vL; SPUle LD.vL (SLit (2 ^ 40))].
  (* intern_rest's post writes the cursor end back as vB + (pLEN + pPOS); the node keeps that order so infer_sub binds
     pPOS and pLEN the right way round. *)
  Definition ceR : list cell := [LoU.c8 8 (LD.txt (SAlu ALU_ADD LD.pLEN LD.pPOS))].
  (* s6 = intern_rest's result (the material name) is stored after the call *)
  Definition E_fs : sstate :=
    site 0x152cc 0x143fc [(10%nat, LoU.bx); (22%nat, LD.pX)] (LoU.cpC LD.pCP) ceR (SPUle LD.pX (SLit (2 ^ 47)) :: cfacts).
  Definition E_nt : sstate :=
    site 0x18298 0x14564 [(10%nat, LoU.cx); (11%nat, LoU.spo (1672 - LoU.FR)); (12%nat, LoU.spo (1656 - LoU.FR))]
      (LoU.cpC LD.pCP) (LoU.ceC LD.pE) cfacts.
  (* scan_int on the token next_token left in the frame: local cursor = token start, end = token end *)
  Definition E_si : sstate :=
    sitel 0x1a54c 0x148b4
      [(10%nat, LoU.spo (1632 - LoU.FR)); (11%nat, SAlu ALU_ADD LD.pSL (LD.txt LD.pST)); (12%nat, LoU.spo (1616 - LoU.FR))]
      (LoU.cpC LD.pCP) ceR [LoU.c8 (1632 - LoU.FR) (LD.txt LD.pST)] (tfacts ++ cfacts).
  Definition E_bw : sstate := site 0x1a690 0x14978 [(10%nat, LoU.bx); (11%nat, SLit 0x10633)] [] [] [].
  (* s7 = number of coordinates parsed before the failing scan_double, read by the zero-fill loop after the call: one
     call state per value (0, 1, 2) so the loop runs a literal number of times *)
  Definition E_daK (k : Z) : sstate :=
    site 0x1bf5c 0x145a8 [(10%nat, SLit 0); (11%nat, LoU.alx); (12%nat, LD.pLINE); (13%nat, SLit 0x10298); (23%nat, SLit k)] [] [] [].
  Definition E_da0 : sstate := E_daK 0.
  Definition E_da1 : sstate := E_daK 1.
  Definition E_da2 : sstate := E_daK 2.
  (* the dispatch keeps the token in s8 (start) / s9 (length) / s6 (end) and the line end in s7 across slice_eq *)
  (* written for the binder (infer_sub: bare registers first, then registers in order, `a + SVar i` by offset, else by
     structure, operator ignored): s9 binds pSL; s6 = ((pST + vB) + pSL) + 0 binds nothing against either engine
     shape of the token end ((vB + end) + 1 after the token loop, or the line end pLEN + (vB + pPOS)); s8 = vB + pST
     binds pST; s7 is the line end in the engine's shape *)
  Definition eR : sv := SAlu ALU_ADD LD.pLEN (LD.txt LD.pPOS).
  Definition tok_regs : list (nat * sv) :=
    [(22%nat, SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_ADD LD.pST LD.vB) LD.pSL) (SLit 0)); (23%nat, eR);
     (24%nat, LD.txt LD.pST); (25%nat, LD.pSL)].
  Definition tok_facts : list sprop :=
    [SPUle (SLit 1) LD.pSL; SPUle LD.pPOS LD.pST; SPUle (SAlu ALU_ADD LD.pST LD.pSL) LD.pE].
  Definition se_site (ra lit : Z) : sstate :=
    site 0x18350 ra ([(10%nat, LD.txt LD.pST); (11%nat, LD.pSL); (12%nat, SLit lit)] ++ tok_regs) (LoU.cpC LD.pCP) (LoU.ceC LD.pE)
      (tfacts ++ tok_facts ++ cfacts).
  Definition E_se1 : sstate := se_site 0x140d8 0x102f7.
  Definition E_se2 : sstate := se_site 0x14358 0x1048f.
  Definition E_se3 : sstate := se_site 0x14380 0x102e6.
  Definition E_se4 : sstate := se_site 0x143c4 0x106a5.
  Definition E_se5 : sstate := se_site 0x143dc 0x104e0.
  Definition E_se6 : sstate := se_site 0x14550 0x10449.
  Definition E_se7 : sstate :=
    sitel 0x18350 0x1457c [(10%nat, LD.txt LD.pST); (11%nat, LD.pSL); (12%nat, SLit 0x104c5)] (LoU.cpC LD.pCP) ceR
      [LoU.c8 (1672 - LoU.FR) (LD.txt LD.pST); LoU.c8 (1656 - LoU.FR) LD.pSL] (tfacts ++ cfacts).
  Definition E_se8 : sstate := se_site 0x146a4 0x105cc.
  Definition E_se9 : sstate := se_site 0x14838 0x105d3.
  (* scan_double: cursor, token end, double local *)
  Definition sd_siteR (ra off : Z) (regs : list (nat * sv)) (facts : list sprop) : sstate :=
    site 0x183d0 ra ([(10%nat, LoU.cx); (11%nat, LD.txt LD.pE); (12%nat, LoU.spo (off - LoU.FR))] ++ regs) (LoU.cpC LD.pCP)
      (LoU.ceC LD.pE) (facts ++ cfacts).
  Definition sd_site (ra off : Z) : sstate := sd_siteR ra off [] [].
  (* the first scan_double gets the line end from s7 (engine shape eR), the others reload it from the cursor cell *)
  Definition E_sdA1 : sstate :=
    site 0x183d0 0x14158 [(10%nat, LoU.cx); (11%nat, eR); (12%nat, LoU.spo (1656 - LoU.FR))] (LoU.cpC LD.pCP) (LoU.ceC LD.pE) cfacts.
  Definition E_sdA2 : sstate := sd_site 0x14178 1656.
  Definition E_sdA3 : sstate := sd_site 0x14198 1656.
  Definition E_sdA4 : sstate := sd_site 0x141b8 1656.
  Definition E_sdA5 : sstate := sd_site 0x141d8 1656.
  Definition E_sdA6 : sstate := sd_site 0x141f8 1656.
  Definition E_sdA7 : sstate := sd_site 0x14218 1656.
  Definition E_sdA8 : sstate := sd_site 0x14238 1656.
  Definition E_sdB1 : sstate := sd_site 0x14428 1672.
  Definition E_sdB2 : sstate := sd_site 0x14448 1672.
  (* s6 = texcoord count before the two pushes after vrA (canonical count - 2), read by the optional-w push *)
  Definition E_sdB3 : sstate :=
    sd_siteR 0x144fc 1672 [(22%nat, SAlu ALU_ADD (SVar 120) (SLit (-2)))] [SPUle (SLit 2) (SVar 120); SPUle (SVar 120) (SLit (2 ^ 47))].
  (* vec_reserve: builder vector header, wanted count (the vector's canonical count + 2 / + 3), allocator; s6 keeps the
     vertex (vrB) / texcoord (vrA) count for the pushes after the call, s7 (vrB) the number of parsed coordinates *)
  Definition nfacts : list sprop := [SPUle (SVar 111) (SLit (2 ^ 47))].
  Definition E_vrA : sstate :=
    site 0x167f8 0x14474 [(10%nat, LoU.spo (LoU.bofs + 216)); (11%nat, SAlu ALU_ADD (SVar 120) (SLit 2)); (12%nat, LoU.alx);
                          (22%nat, SVar 120)] (LoU.cpC LD.pCP) (LoU.ceC LD.pE) (SPUle (SVar 120) (SLit (2 ^ 47)) :: cfacts).
  Definition E_vrB : sstate :=
    site 0x167f8 0x14644 [(10%nat, LoU.spo (LoU.bofs + 120)); (11%nat, SAlu ALU_ADD (SMd M_MUL (SVar 111) (SLit 3)) (SLit 3));
                          (12%nat, LoU.alx); (22%nat, SVar 111); (23%nat, LD.pN)] [] []
      (nfacts ++ [SPUle (SLit 3) LD.pN; SPUle LD.pN (SLit 8)]).
  (* opt_push: vector header, cm, value count, value and default locals, presence, allocator *)
  Definition op_siteC (ra o cm vo do : Z) (cnt : sv) (regs : list (nat * sv)) (facts : list sprop) : sstate :=
    site 0x1bd78 ra ([(10%nat, LoU.spo (LoU.bofs + o)); (11%nat, SLit cm); (12%nat, cnt); (13%nat, LoU.spo (vo - LoU.FR));
                      (14%nat, LoU.spo (do - LoU.FR)); (15%nat, LD.pW); (16%nat, LoU.alx)] ++ regs) [] []
      (SPUle LD.pW (SLit 1) :: facts).
  (* The vertex pushed after vrB: the position vector's float count cell (builder+128) is 3 n + 3 for the canonical vertex
     count n, and opt_push gets the vertex index n (also kept in s6). *)
  Definition set_cell (lo off : Z) (v : sv) (o : sobj) : sobj :=
    if sv_eqb (ob_lo o) (SLit lo) then
      mkObj (ob_base o) (ob_lo o) (ob_hi o)
        (map (fun c => if sv_eqb (c_off c) (SLit off) then mkCell (c_off c) (c_width c) v else c) (ob_cells o)) (ob_dflt o)
    else o.
  Definition with_cell (lo off : Z) (v : sv) (S : sstate) : sstate :=
    {| ss_pc := ss_pc S; ss_regs := ss_regs S; ss_fregs := ss_fregs S; ss_fcsr := ss_fcsr S; ss_resv := ss_resv S;
       ss_objs := map (set_cell lo off v) (ss_objs S); ss_facts := ss_facts S; ss_next := ss_next S; ss_lenient := ss_lenient S |}.
  (* 3 (n + 1): the engine's 3 n + 3 in the product form the canonical cell 3 n' has, so later nodes bind n' := n + 1 *)
  Definition vpush : sv := SMd M_MUL (SAlu ALU_ADD (SVar 111) (SLit 1)) (SLit 3).
  (* the pushed vertex fits the reserved capacity: the canonical count facts for n + 1 *)
  Definition pfacts : list sprop := [SPUle vpush (SVar 112); SPUle (SAlu ALU_ADD (SVar 111) (SLit 1)) (SLit (2 ^ 47))].
  (* s6 = that index, s7 = parsed coordinates, s8 = 1 stay live across the w push *)
  Definition E_op1 : sstate :=
    with_cell 120 128 vpush
      (op_siteC 0x14798 152 1 1652 1648 (SVar 111) [(22%nat, SVar 111); (23%nat, LD.pN); (24%nat, SLit 1)]
         (nfacts ++ [SPUle vpush (SVar 112); SPUle (SLit 3) LD.pN; SPUle LD.pN (SLit 8)])).
  Definition E_op3 : sstate := with_cell 120 128 vpush (op_siteC 0x149ec 280 3 1632 1616 (SVar 111) [] (nfacts ++ pfacts)).
  (* the same call (0x149e8) reached from the texcoord path 0x1485c: optional w into the vector at bofs+248, count =
     index of the texcoord just pushed = (canonical float count - 2) / 2 *)
  Definition E_op3b : sstate :=
    op_siteC 0x149ec 248 1 1632 1616 (SAlu ALU_SRL (SAlu ALU_ADD (SVar 120) (SLit (-2))) (SLit 1)) []
      [SPUle (SLit 2) (SVar 120); SPUle (SVar 120) (SLit (2 ^ 47))].
End LoSite.
