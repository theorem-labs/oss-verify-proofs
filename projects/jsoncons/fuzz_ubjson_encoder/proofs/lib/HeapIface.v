(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_HeapIface () := "C47Corelib4Init9Datatypes3fstc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_sptopC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init5Logic2eq01i79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface;heap_layout00C13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC35stdpp4base6ElemOfI35stdpp4base<list_elem_of00I35stdpp4base5NoDup00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8stack_okC13~~~C56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_stackC13~~~C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hl_segsC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7init_vmC13~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~I47Corelib4Init5Logic2ex00C47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem5State:vm_init_spC4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedK4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps01I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC4ELinuxProcessSemantics?LinuxProcessSem5StateBstack_max_size_val".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Record heap_layout : Type := HL {
  hl_segs      : list Segment;        (* [comment removed for export] *)
  hl_malloc    : Z;                   (* [comment removed for export] *)
  hl_free      : Z;                   (* [comment removed for export] *)
  hl_aligned_alloc : Z;               (* [comment removed for export] *)
  hl_tp        : Z;                   (* [comment removed for export] *)
  hl_errno     : Z;                   (* [comment removed for export] *)
  hl_img_lo    : Z;                   (* [comment removed for export] *)
  hl_img_hi    : Z;
  hl_alloc_static : Z -> Prop;        (* [comment removed for export] *)
  hl_alloc_ro  : Z -> Prop;           (* [comment removed for export] *)
  hl_stack     : Z;                   (* [comment removed for export] *)
  hl_sptop     : Z;                   (* [comment removed for export] *)
  hl_k_per_malloc : Z;                (* [comment removed for export] *)
  hl_b_overhead : Z;                  (* [comment removed for export] *)
  hl_K0 : Z; hl_B0 : Z                (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Abbreviation hl_ceil L := (hl_sptop L - 8388608).
(* [comment removed for export] *)

Lemma hl_ceil_eq : forall L, hl_ceil L = hl_sptop L - 2 ^ 23.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIface ()) [] "h01Lp;1p;2p-1R0p10000R1p4p710p8P0P1p4p7210p8g000Mj16Tg001Zj15Tg002?j11Tg002]j10Tg003Bj24Tg003_j22Tg004<j23Tg004Vg005hf0#6g006F#5R1#1%01#0#0#1'4'2'3W0o"). Qed.

Definition credit : Type := (Z * Z)%type.   (* [comment removed for export] *)
Definition credit_ok (L : heap_layout) (cr : credit) (n : Z) : Prop :=
  hl_k_per_malloc L <= fst cr /\ n + hl_b_overhead L <= snd cr.
Definition debit (L : heap_layout) (cr : credit) (n : Z) : credit :=
  (fst cr - hl_k_per_malloc L, snd cr - (n + hl_b_overhead L)).

(* [comment removed for export] *)
Definition in_block (LB : list (Z * Z)) (a : Z) : Prop :=
  exists b, In b LB /\ fst b <= a < fst b + snd b.

(* [comment removed for export] *)
Definition client_addr (L : heap_layout) (LB : list (Z * Z)) (sp scratch : Z) (a : Z) : Prop :=
  in_block LB a
  \/ (hl_ceil L <= a < 2 ^ 64 /\ ~ (sp - scratch <= a < sp))
  \/ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a).

(* [comment removed for export] *)
Definition in_errno (L : heap_layout) (a : Z) : Prop := hl_errno L <= a < hl_errno L + 4.

(* [comment removed for export] *)
Definition heap_pres_core (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> client_addr L LB sp (hl_stack L) a -> ~ in_errno L a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
  /\ (forall a, sp - hl_stack L <= a < sp -> M' (Z_to_bv 64 a) <> None).   (* [comment removed for export] *)
  (* [comment removed for export] *)

Definition heap_pres (L : heap_layout) (LB : list (Z * Z)) (sp : Z) (M M' : word -> option byte) : Prop :=
  heap_pres_core L LB sp M M'
  /\ rdn (hl_segs L) M' (Z_to_bv 64 (hl_errno L)) 4 = rdn (hl_segs L) M (Z_to_bv 64 (hl_errno L)) 4.   (* [comment removed for export] *)

Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.

Definition blocks_apart (A n : Z) (LB : list (Z * Z)) : Prop :=
  forall b, In b LB -> A + n <= fst b \/ fst b + snd b <= A.

(* [comment removed for export] *)
Definition block_range (L : heap_layout) (A n : Z) : Prop :=
  4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A) /\ A mod 16 = 0 /\ 0 < n /\ A + n <= hl_ceil L.

Fixpoint lb_remove (A : Z) (LB : list (Z * Z)) : list (Z * Z) :=
  match LB with
  | [] => []
  | b :: LB' => if Z.eqb (fst b) A then LB' else b :: lb_remove A LB'
  end.

(* [comment removed for export] *)
Definition callee_saved_idx : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition regs_preserved (R R' : bvmap 5 word) : Prop :=
  forall r : bv 5, In (bv_unsigned r) callee_saved_idx -> getr R' r = getr R r.

(* [comment removed for export] *)
Definition model_but_vm (m m' : Model) : Prop :=
  m' = with_vmmaps (m_vmmaps m') m.

(* [comment removed for export] *)
Section Iface.
Variable L : heap_layout.
Variable scfg : SpuriousCfg. Context {bmK : BMode}.   (* [comment removed for export] *)      (* [comment removed for export] *)

Record heap_iface : Type := HI {
  (* [comment removed for export] *)
  hi_heap : list (Z * Z) -> credit -> (word -> option byte) -> VmMaps -> Prop
}.

Variable HI : heap_iface.

(* [comment removed for export] *)
Definition stack_ok (M : word -> option byte) (sp : Z) : Prop :=
  sp mod 16 = 0 /\ hl_ceil L + hl_stack L <= sp /\ sp <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47 /\
  (forall d (m : nat), 0 <= d -> d + Z.of_nat m <= hl_stack L ->
      store_ok (hl_segs L) M (Z_to_bv 64 (sp - hl_stack L + d)) m = true).

(* [comment removed for export] *)
Lemma stack_ok_floor : forall M sp, stack_ok M sp -> 0x7fff7f800000 + hl_stack L <= sp.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIface ()) ["Iface"] "h01dh11mh22H0h34__x1h44__x2h54__x3h61Hh73Hloh81Mh92_Hh:3_H0h;3_H1h<3_H2h=7__arithh>4__ffh?8__varmaph@5__withA2spp;1p;2p;3p;4p;7p;8p-1R0p1006kp4p710p8P0p1007BR1p4p710p8P0P1p4p7210p8P0p1007^R1p4p710R2p8P0P1p4p7210R1p8P0p10082p4p710R0p8p1008Np4p710R3P2p8P3P1p8P3P0p8g001Zj11Tg008cj1GTg009Aj1DTg009dj1eTg00:Fj2ZTg002?j16Tg00;Sj2CTg00<3j3:Tg000Mj1RTg00<Mj1LTg00=Zj20Tg002]j15Tg003Bj2XTg00>6R0j22Tg00>Qj1WTg00?1j28Tg00?Nj1VTg00@Zj1BTg00A9j2>Tg00Abj3ATg00BKj2TTg00C7j1STg00CWj3QTg00D7j1PTg00DWj2@Tg00E5j4NTg00ESj1MTg00F1j1OTg00F\j2=Tg00G?j2;Tg00Gbj1KTg00HDj3UTg00Hgj3JTg00IJj2dTg004<j2cTg00Ilj2bTg00JXj3\Tg00K7j4[Tg003_j2ETg00Kij2YTg00LOj4]Tg00MOj4^Tg00N:j7_Tg00N^j8`Tf0R3#1#1p=9%13#1#1#1#1#1#1#1p=4f2R1f1R2'E/83p=H%53#5#5#5p=7%13#1#1#1p=Fg00OBR4f6R5f5R6f4R7f3R8/E1/82'YP3C]g00ObR93:p=3g005hR:P2g00PBP3C^p=<P2g00PiR;g00QHR<P<g00QhR=P3g00RHF_p=?P8P;P<P<P=P1P2P3G`p=IA:439p=ag006FR;#1R>#9R?#1R@#9RA#GRB#D%G?#D#e[1Z23P0%6@R@,C2g00RhR?5::p,1LRC#RRD%1A#4#4#6RA%LCRE3HRF/02102D%5;RG#5#7#7#7RH#5#1#9#F#4#4#4#6RI/0DRJ%6>%7>#6'X,0DRK'2RLg00SFRM10?2RN%W2,81/0ERO%VCRCP5PBP6PEP8P1F3[[]1^0:'2'2'2%1H#7#7#1#9#F#4#4#6RH/8ERP/01P31C8@=::?10F7107DPCf9R7PBf8R@PEP8P1F3\O\N^1M^0:,2L'2'2P010F6106DPCf:R6PBP7PEP8P1F3\O\N^1M^0:,2L'210P5P3f7,0F10@DPCf=R@PBf<PEP8P1F3\O\N^1M^0:,2L'2P0107DPCf>R7PBP@PEP8P1F3\O\N^1M^0:,2L10P6P3f;/0DPCfAR6PBf@PEP8P1F3\O\N^1M^0:,2LP0PLPCfBR@PBP6PEP8P1F3\O\N^1M^0:10P7P3P0PJPKPCfFR0PBfEPEP8P1F3\O\N^1M^0:10P@[P3PCfIPBfHPEP8P1F3\O\N^1M^0:g00SeRMg00TQRN#BRO#B,>:1>:O1>:N5A:5A:g00U0'T%SM3Q%PMP:1@:1P21@:8CN%M:%O:RM1=:I1;:GRG'<,?M%K<R<PM1=:A9U:G1;:;R;5J:1;:>R>'<,?MP<1=:H=J:;/<>,?MCICI1dM=P3P11c491b31#adA\:?2C[b>b?b@X3:X4:X5:10I1AH8A2/0118H1/08[[^3:^4:^5:P3PDP0PEP8P7O5b=W<X;KX7JP2P3O2n2001000000121000000X2LP2P3O2n2001000000121000000W2W:P2P3O2n2001000000121000000W2W6P2P3O2n2001000000121000000W2W9P2P3O2n2001000000121000000W2XA:W8o"). Qed.

(* [comment removed for export] *)
Definition malloc_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_malloc L)) M (seg_rom (hl_segs L))) model) K.


(* [comment removed for export] *)
Definition aligned_alloc16_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    getr R 10%bv = Z_to_bv 64 16 -> getr R 11%bv = Z_to_bv 64 n -> 0 < n <= 2 ^ 27 ->
    credit_ok L cr n ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (A : Z),
        getr R' 10%bv = Z_to_bv 64 A ->
        regs_preserved R R' ->
        block_range L A n -> blocks_apart A n LB ->
        defined M' A n ->
        heap_pres_core L LB (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI ((A, n) :: LB) (debit L cr n) M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_aligned_alloc L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model)
         (LB : list (Z * Z)) (cr : credit) (A n : Z) (K : ShapeAlg.TSet),
    hi_heap HI LB cr M (m_vmmaps model) ->
    m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] ->
    In (A, n) LB ->
    getr R 10%bv = Z_to_bv 64 A ->
    getr R 4%bv = Z_to_bv 64 (hl_tp L) ->
    Hoare.ret_ok (getr R 1%bv) ->                      (* [comment removed for export] *)
    stack_ok M (bv_unsigned (getr R 2%bv)) ->
    K [] ->
    (forall (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        heap_pres L (lb_remove A LB) (bv_unsigned (getr R 2%bv)) M M' ->
        model_but_vm model model' ->
        hi_heap HI (lb_remove A LB) cr M' (m_vmmaps model') ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M' (seg_rom (hl_segs L))) model') K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition free_null_spec : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : ShapeAlg.TSet),
    m_halted model = None -> m_vm_lazy model = [] ->
    getr R 10%bv = Z_to_bv 64 0 ->
    Hoare.ret_ok (getr R 1%bv) ->
    K [] ->
    (forall R', regs_preserved R R' ->
        srealizes (hl_segs L) scfg (mkCfg (@mkst fx R' (getr R 1%bv) M (seg_rom (hl_segs L))) model) K) ->
    srealizes (hl_segs L) scfg (mkCfg (@mkst fx R (Z_to_bv 64 (hl_free L)) M (seg_rom (hl_segs L))) model) K.

(* [comment removed for export] *)
Definition alloc_private (LB : list (Z * Z)) (a : Z) : Prop :=
  (a < hl_ceil L /\ ~ in_block LB a /\ ~ (hl_img_lo L <= a < hl_img_hi L /\ ~ hl_alloc_static L a))
  \/ hl_alloc_ro L a.

Definition heap_frame : Prop :=
  forall LB cr M M' VM,
    hi_heap HI LB cr M VM ->
    (forall a, 0 <= a < 2 ^ 64 -> alloc_private LB a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a : word, M a <> None -> M' a <> None) ->
    hi_heap HI LB cr M' VM.

(* [comment removed for export] *)
Definition heap_blocks_wf : Prop :=
  forall LB cr M VM, hi_heap HI LB cr M VM ->
    (forall b, In b LB -> block_range L (fst b) (snd b) /\ defined M (fst b) (snd b)
                       /\ blocks_apart (fst b) (snd b) (lb_remove (fst b) LB))
    /\ NoDup (map fst LB) /\ 0 <= fst cr /\ 0 <= snd cr.

(* [comment removed for export] *)
Definition heap_perm : Prop :=
  forall LB LB' cr M VM, hi_heap HI LB cr M VM -> (forall b, In b LB <-> In b LB') -> NoDup (map fst LB') ->
    hi_heap HI LB' cr M VM.

Record heap_iface_ok : Prop := HIOK {
  hio_malloc : malloc_spec;
  hio_aligned : aligned_alloc16_spec;
  hio_free : free_spec;
  hio_free_null : free_null_spec;
  hio_frame : heap_frame;
  hio_wf : heap_blocks_wf;
  hio_perm : heap_perm
}.
End Iface.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section InitVm.
Context {bmK : BMode}.
Definition init_vm (L : heap_layout) (lim : Z) (VM : VmMaps) : Prop :=
  exists brk0 mbase isp,
    VM = mkVmMapsFull (segments_reserved (hl_segs L)) [] [] brk0 brk0 lim mbase isp /\
    valid_brk (hl_segs L) brk0 /\ valid_mmap_base mbase /\ valid_sp isp /\ bv_unsigned isp = hl_sptop L /\ (bm_on = true \/ 2 ^ 34 <= lim).
End InitVm.
(* [comment removed for export] *)

Lemma init_vm_alloc_top : forall L lim VM, init_vm L lim VM -> alloc_top VM = hl_ceil L.
Proof.
ltac2:(KReplay.run1 (kr_t_HeapIface ()) [] "p'0h01Hh13isph25mbaseh32VMh44brk0h51zh63Hsph71Lh82_Hh93_H0h:3_H1h;3_H2h<3limi001xp;4p;1p;2p;3p;6p;8g00U\j4WTg001Zj1ATg008cj1NTg009Aj1VTg00?Nj11Tg00Vhj2RTg00C7j1OTg00WHj28Tg00X>j19Tg00Y:j1:Tg00Yoj25Tg00ZYj1UTg00<3j3>Tg002?j1GTg002]j1TTg003Bj2STg00[_R0j2@Tg000Mj10Tg003_j23Tg00>6R1j24Tg004<j2MTg00\9j6ETg00\Wj1LTg00]Pj1PTg00^Nj8QTg00=Zj2FTg00_Ej2DTg00__j1KTf0R2#A#Ap=6f7R3#Pf6R4f5R5f4R6f3R7f2R8f1R9P2GQp=2g00`WR:?>92p=<g005hR;%077>61F92,D8'4,45,44p=;1492,48p==%K9=>;2p=7A>;671F92,D8'4,45,44p=J1889/42p=I1589=>;2p=B1F92,D8p=?%099>;8/42p=HA>;92p=Cg004Vg00aNR<P8P9P2CWP0g006F#AR=#6R>#A#6R?#NR@#VRA%14RB1RAA#ORCPCP8P8P5P9P2G2,<618B8%99RB%:2RD15@2REP4g00OB%U<g00Ob3>R<%G=%T>#A#G'SR>P5F;3=X1A,@AX2A,@AX4A%06%A?#6#6#6#6#6#6#6#6#GR?'3,78P2f8R=#1RFPCPCP8P8P3P9P2G2,<418F8PBPDPE%0=RFP<P>P3FJ3=X1A,@AX2A,@AP0PAf9RG#1RHPCPCP7P7P=P9P2G2,<318H7PBPDPEPGP<P>P=F;3=X1A,@AX2A13F?,74P2f;RF#1RHPCPCP5P5f:RIP9P2G2,<G18H5PBPDPEPFP<P>PIF;3=X1A,@AP0PAf<R0#1RBPCPCP4P4PFP8P2G2,<I18B4%98PDPE%00R8P<P>PFFJ3=X1A138?,7IP2f>R8#1RBPCPCP=P=f=RHP6P2G2,<018B=%96PDPEP8P<P>PHF;3=P1f?RE#1RDPCPCPGPGP8P5P9G2,<H%95%:915@9PEP<P>P8F;9IDGf@RD#0/3?,78P2fARB#1PCPCPFPFPDP3P7G2,<EP:fBR7#1R3PCPCP0P0PBP=P6G2fCRF#1/8HRJ%9G%:515@5PFP<P>P7F;R5'4fDRK#0/3?RL,79[X3:%9=%:615@6P7P<P>PBF;9I30P1PJP5%1KPCPCP8P8PFPIP4G2/7LP2fERL#1/8E%90%:=15@=fFR=P<P>PLF;P1%9H%:GfGR4#09B@GA?<>=3=fHRG#1PCPCP7P7P4P8PIG2%0G/3?'7P2%9E%:0fJRG#09B@0fIR09?<>3=P1%:H15@HfKRHA?<>G3HfLRI#1PCPCP=P=PHP7P8G2%0I/3?'7P2%:E15@DfNREfMRI9?<>3HP1fOR1#09B@BA?<>EfPRE#1PCPCPGPGP1P=P7G2%0E/3?'7P2fQRE#09B@FA?<>EP;fSRE#0R>g00bZR<,32fT#0RF/3?R7'CX5;P;P?13F2/C7X5;13>?R>,M;P<g00cWEE15@LP9EE%1EPCPCPIPIfRP0PLG2RL#L,5@/3</C>e17L>eW;W6P9P2O2n2001000000121000000W0W:P9P2O2n2001000000121000000W0W9P9P2O2n2001000000121000000W0W8P9P2O2n2001000000121000000W0PDP2EEW0P9P2O2n2001000000121000000W0X1AP9P2O2n2001000000121100000W0X2AP9P2O2n2001000000121100000W0X4AP9P2O2n2001000000121100000W0X3:X<;W7o"). Qed.
