(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsCells.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record as_addrs := ASADDRS {
  ia_malloc : Z; ia_malloc_thunk : Z;   (* [comment removed for export] *)
  ia_free : Z; ia_free_thunk : Z;
  ia_opnew : Z; ia_opnew_thunk : Z;     (* [comment removed for export] *)
  ia_opdel : Z; ia_opdel_sz : Z;        (* [comment removed for export] *)
  ia_stkmal : Z -> Z;                   (* [comment removed for export] *)
  ia_f5 : Z; ia_f8 : Z;                 (* [comment removed for export] *)
  ia_memcpy_icpt : Z; ia_asan_memcpy : Z; ia_memset_icpt : Z; ia_asan_memset : Z; ia_memmove_icpt : Z; ia_asan_memmove : Z;
  ia_strlen_icpt : Z;
  ia_real_memcpy : Z; ia_real_memset : Z; ia_real_strlen : Z;   (* [comment removed for export] *)
  ia_errno_loc : Z;                     (* [comment removed for export] *)
  ia_img_lo : Z; ia_img_hi : Z;         (* [comment removed for export] *)
  ia_ro_hi : Z;                         (* [comment removed for export] *)
  ia_tp : Z;                            (* [comment removed for export] *)
  ia_rtc_sb : Z; ia_rtc_uar : Z;        (* [comment removed for export] *)
  ia_instance : Z; ia_depot_tab : Z; ia_stackstore : Z; ia_ialloc_flag : Z; ia_ialloc_inst : Z;
  ia_asan_flags : Z; ia_common_flags : Z; ia_pagesz_cell : Z; ia_highmem_end : Z;   (* [comment removed for export] *)
  ia_newh_cell : Z; ia_newh_val : Z;    (* [comment removed for export] *)
  ia_spins : list Z;                    (* [comment removed for export] *)
  ia_priv : list (Z * Z);
  ia_const : list (Z * Z)
}.

Definition asan_addrs : as_addrs :=
  ASADDRS 0x6e4cc 0x6e2f0 0x6e2fc 0x6e2ec 0xfab00 0xfab70 0xdafd8 0xdafdc
          (fun k => match k with 0 => 0x5716c | 1 => 0x572e0 | 2 => 0x57470 | _ => 0x5760c end)
          0x703e4 0x703fc
          0x6d968 0x6c76c 0x6d1b8 0x6cc08 0x6d4a8 0x6ce48
          0x5c57c
          0xf52e0 0xf56e4 0xf5930 0xe6d10
          0x10000 0x65d000 0xfb000 0x63a740
          0x107578 0x107580
          0x103f18 0x1e9458 0x1d9448 0x197008 0x108780
          0x104d78 0x1990a8 0x197020 0x108260
          0x639c00 0x0
          [0x4ec04; 0x50228; 0x6fab4; 0x7bfb4; 0x7c084; 0x8a4bc; 0x8a64c; 0x765fc; 0x76610; 0x76624; 0x895b0; 0x943a4]
          [(0x1011f0, 0x1038c0); (0x103f18, 0x104d78); (0x104df8, 0x107578); (0x107588, 0x108258); (0x10825a, 0x1990a8); (0x1991c8, 0x199420); (0x199421, 0x629bd0); (0x63a6e8, 0x63a6f0); (0x63a730, 0x63a754); (0x65bae8, 0x65baf0)]
          [(0x10000, 0xfb000); (0xfb000, 0x101000); (0x101028, 0x1011f0); (0x108258, 0x10825a); (0x104d78, 0x104df8); (0x1990a8, 0x1991c8); (0x199420, 0x199421); (0x107578, 0x107588); (0x65aa00, 0x65aa08); (0x63a760, 0x63a770)].

(* [comment removed for export] *)
Definition asan_consts (P6 SPB M8 M10 : Z) : list (Z * nat * Z) :=
  let KSPACE := 2 ^ 37 in
  [(0xff250, 8%nat, 0x197020);
   (0xff260, 8%nat, 0x1990a8);
   (0xff268, 8%nat, 0x104d78);
   (0xff270, 8%nat, 0x107578);
   (0xff278, 8%nat, 0x108268);
   (0xff280, 8%nat, 0x108270);
   (0xff288, 8%nat, 0x108260);
   (0xff290, 8%nat, 0x1011b0);
   (0xffdd8, 8%nat, 0x108259);
   (0xffec8, 8%nat, 0x10);
   (0x10490, 8%nat, 0x218a392cd3d5dbf);
   (0x10504, 1%nat, 0x3);
   (0x10608, 1%nat, 0x4);
   (0x10631, 1%nat, 0xb);
   (0x103b8, 8%nat, 0xcc6e96b9cc6e96b9);
   (0x10408, 8%nat, 0x101010101010100);
   (0x103e8, 8%nat, 0x8080808080808080);
   (0x101030, 8%nat, 0xf5930);
   (0x1011a8, 8%nat, 0xf52e0);
   (0x1011b0, 8%nat, 0xf56e4);
   (0x103f18, 8%nat, P6);
   (0x103f20, 8%nat, 0x2000011000);
   (0x103f38, 8%nat, SPB);
   (0x103f40, 4%nat, 0xffffffff);
   (0x103f48, 8%nat, SPB + KSPACE);
   (0x103f50, 1%nat, 0x0);
   (0x103f58, 8%nat, 0x1000);
   (0x103f60, 8%nat, M8);
   (0x103f68, 8%nat, M8);
   (0x103f70, 8%nat, 0x800000);
   (0x104230, 8%nat, 0x10000000);
   (0x104238, 8%nat, 0xe666661);
   (0x104240, 8%nat, 0x100000);
   (0x104d38, 8%nat, 0x10000000000);
   (0x104d40, 2%nat, 0x10);
   (0x104d42, 2%nat, 0x800);
   (0x104d44, 1%nat, 0x1);
   (0x104d84, 4%nat, 0x10);
   (0x104d88, 4%nat, 0x800);
   (0x104da4, 4%nat, 0x1000);
   (0x104da8, 4%nat, 0x0);
   (0x104dac, 1%nat, 0xbe);
   (0x104dac, 4%nat, 0xbe);
   (0x104dcd, 1%nat, 0x1);
   (0x104db0, 4%nat, 0x55);
   (0x104db4, 1%nat, 0x1);
   (0x104dd8, 1%nat, 0x1);
   (0x106ddc, 1%nat, 0x1);
   (0x106de0, 1%nat, 0x1);
   (0x106de4, 4%nat, 0x0);
   (0x108258, 1%nat, 0x1);
   (0x108259, 1%nat, 0x1);
   (0x108260, 8%nat, 0x7fffffffffff);
   (0x108268, 8%nat, 0x0);
   (0x108270, 8%nat, 0x0);
   (0x10827c, 4%nat, 0x1e);
   (0x1897e1, 1%nat, 0x1);
   (0x1897e2, 1%nat, 0x0);
   (0x197020, 8%nat, 0x1000);
   (0x199040, 8%nat, 0x0);
   (0x199048, 8%nat, 0x0);
   (0x1990ca, 1%nat, 0x1);
   (0x199120, 8%nat, 0xffffffffffffffff);
   (0x1991a3, 1%nat, 0x1);
   (0x63a6e8, 8%nat, 0x65bae8);
   (0x65bae8, 8%nat, M10);
   (0x63a750, 4%nat, 0x0);
   (0xff2c0, 8%nat, 0x197018);
   (0x197018, 4%nat, 0x0);
   (0x10310, 8%nat, 0xc6a4a7935bd1e995);
   (0x10350, 8%nat, 0x35253c9ade8f4ca8);
   (0x10450, 8%nat, 0x9747b28c9747b28c);
   (0x107578, 8%nat, 0x7fff8000);
   (0x107580, 4%nat, 0x1);
   (0xff2b0, 8%nat, 0x1);
   (0xff2b8, 8%nat, 0x19909c);
   (0x19909c, 4%nat, 0x0);
   (0x199138, 8%nat, 0x0);
   (0xfffb8, 8%nat, 0x65a780);
   (0x33518, 2%nat, 0xff04);
   (0x334b4, 4%nat, 0xb3134);
   (0x65aa00, 8%nat, 0x1000);
   (0x10470, 8%nat, 0xafffff00000fffff);
   (0x100010, 8%nat, 0x1);
   (0x100018, 8%nat, 0xfffffffffffff800);
   (0x100020, 8%nat, 0x8);
   (0x1010d0, 8%nat, 0xf5fbc);
   (0x199131, 1%nat, 0x1);
   (0x1991ac, 1%nat, 0x0);
   (0xff258, 8%nat, 0x1011e8);
   (0x1011e8, 8%nat, 0x1a2c0);
   (0x104e30, 8%nat, 0x0);
   (0x199198, 4%nat, 0x0);
   (0x1e23c, 8%nat, 0x612079726f6d656d);
   (0x1e244, 8%nat, 0x7365726464612074);
   (0x1e24c, 4%nat, 0x70252073);
   (0x1e250, 1%nat, 0x0);
   (0x22760, 4%nat, 0x60940);
   (0x104b0, 8%nat, 0xaaaaaaaaaaaaaaaa);
   (0x63a738, 8%nat, 0x63a760);
   (0x63a768, 8%nat, 0x63af40)].

Definition both_addrs : as_addrs :=
  ASADDRS 0x6ef3c 0x6ed60 0x6ed6c 0x6ed5c 0x1017a8 0x101818 0xe1c80 0xe1c84
          (fun k => match k with 0 => 0x57bdc | 1 => 0x57d50 | 2 => 0x57ee0 | _ => 0x5807c end)
          0x70e54 0x70e6c
          0x6e3d8 0x6d1dc 0x6dc28 0x6d678 0x6df18 0x6d8b8
          0x5cfec
          0xfbf88 0xfc38c 0xfc5d8 0xed9b8
          0x10000 0x663000 0x102000 0x641380
          0x10e1b8 0x10e1c0
          0x10ab58 0x1f0098 0x1e0088 0x19dc48 0x10f3c0
          0x10b9b8 0x19fce8 0x19dc60 0x10eea0
          0x640840 0x0
          [0x4f674; 0x50c98; 0x70524; 0x7ca24; 0x7caf4; 0x8af2c; 0x8b0bc; 0x7706c; 0x77080; 0x77094; 0x8a020; 0x94e14]
          [(0x107e98, 0x10a568); (0x10ab58, 0x10b9b8); (0x10ba38, 0x10e1b8); (0x10e1c8, 0x10ee98); (0x10ee9a, 0x19fce8); (0x19fe08, 0x1a0060); (0x1a0061, 0x630810); (0x641328, 0x641330); (0x641370, 0x641394); (0x662728, 0x662730)]
          [(0x10000, 0x102000); (0x102000, 0x107000); (0x107cd0, 0x107e98); (0x10ee98, 0x10ee9a); (0x10b9b8, 0x10ba38); (0x19fce8, 0x19fe08); (0x1a0060, 0x1a0061); (0x10e1b8, 0x10e1c8); (0x661640, 0x661648); (0x6413a0, 0x6413b0)].

(* [comment removed for export] *)
Definition both_consts (P6 SPB M8 M10 : Z) : list (Z * nat * Z) :=
  let KSPACE := 2 ^ 37 in
  [(0x105ef8, 8%nat, 0x19dc60);
   (0x105f08, 8%nat, 0x19fce8);
   (0x105f10, 8%nat, 0x10b9b8);
   (0x105f18, 8%nat, 0x10e1b8);
   (0x105f20, 8%nat, 0x10eea8);
   (0x105f28, 8%nat, 0x10eeb0);
   (0x105f30, 8%nat, 0x10eea0);
   (0x105f38, 8%nat, 0x107e58);
   (0x106a80, 8%nat, 0x10ee99);
   (0x106b70, 8%nat, 0x10);
   (0x10488, 8%nat, 0x218a392cd3d5dbf);
   (0x104fc, 1%nat, 0x3);
   (0x10600, 1%nat, 0x4);
   (0x10629, 1%nat, 0xb);
   (0x103b0, 8%nat, 0xcc6e96b9cc6e96b9);
   (0x10400, 8%nat, 0x101010101010100);
   (0x103e0, 8%nat, 0x8080808080808080);
   (0x107cd8, 8%nat, 0xfc5d8);
   (0x107e50, 8%nat, 0xfbf88);
   (0x107e58, 8%nat, 0xfc38c);
   (0x10ab58, 8%nat, P6);
   (0x10ab60, 8%nat, 0x2000011000);
   (0x10ab78, 8%nat, SPB);
   (0x10ab80, 4%nat, 0xffffffff);
   (0x10ab88, 8%nat, SPB + KSPACE);
   (0x10ab90, 1%nat, 0x0);
   (0x10ab98, 8%nat, 0x1000);
   (0x10aba0, 8%nat, M8);
   (0x10aba8, 8%nat, M8);
   (0x10abb0, 8%nat, 0x800000);
   (0x10ae70, 8%nat, 0x10000000);
   (0x10ae78, 8%nat, 0xe666661);
   (0x10ae80, 8%nat, 0x100000);
   (0x10b978, 8%nat, 0x10000000000);
   (0x10b980, 2%nat, 0x10);
   (0x10b982, 2%nat, 0x800);
   (0x10b984, 1%nat, 0x1);
   (0x10b9c4, 4%nat, 0x10);
   (0x10b9c8, 4%nat, 0x800);
   (0x10b9e4, 4%nat, 0x1000);
   (0x10b9e8, 4%nat, 0x0);
   (0x10b9ec, 1%nat, 0xbe);
   (0x10b9ec, 4%nat, 0xbe);
   (0x10ba0d, 1%nat, 0x1);
   (0x10b9f0, 4%nat, 0x55);
   (0x10b9f4, 1%nat, 0x1);
   (0x10ba18, 1%nat, 0x1);
   (0x10da1c, 1%nat, 0x1);
   (0x10da20, 1%nat, 0x1);
   (0x10da24, 4%nat, 0x0);
   (0x10ee98, 1%nat, 0x1);
   (0x10ee99, 1%nat, 0x1);
   (0x10eea0, 8%nat, 0x7fffffffffff);
   (0x10eea8, 8%nat, 0x0);
   (0x10eeb0, 8%nat, 0x0);
   (0x10eebc, 4%nat, 0x1e);
   (0x190421, 1%nat, 0x1);
   (0x190422, 1%nat, 0x0);
   (0x19dc60, 8%nat, 0x1000);
   (0x19fc80, 8%nat, 0x0);
   (0x19fc88, 8%nat, 0x0);
   (0x19fd0a, 1%nat, 0x1);
   (0x19fd60, 8%nat, 0xffffffffffffffff);
   (0x19fde3, 1%nat, 0x1);
   (0x641328, 8%nat, 0x662728);
   (0x662728, 8%nat, M10);
   (0x641390, 4%nat, 0x0);
   (0x105f68, 8%nat, 0x19dc58);
   (0x19dc58, 4%nat, 0x0);
   (0x10310, 8%nat, 0xc6a4a7935bd1e995);
   (0x10348, 8%nat, 0x35253c9ade8f4ca8);
   (0x10448, 8%nat, 0x9747b28c9747b28c);
   (0x10e1b8, 8%nat, 0x7fff8000);
   (0x10e1c0, 4%nat, 0x1);
   (0x105f58, 8%nat, 0x1);
   (0x105f60, 8%nat, 0x19fcdc);
   (0x19fcdc, 4%nat, 0x0);
   (0x19fd78, 8%nat, 0x0);
   (0x106c60, 8%nat, 0x6613c0);
   (0x33480, 2%nat, 0xff04);
   (0x3341c, 4%nat, 0xb9e74);
   (0x661640, 8%nat, 0x1000);
   (0x10468, 8%nat, 0xafffff00000fffff);
   (0x106cb8, 8%nat, 0x1);
   (0x106cc0, 8%nat, 0xfffffffffffff800);
   (0x106cc8, 8%nat, 0x8);
   (0x107d78, 8%nat, 0xfcc64);
   (0x19fd71, 1%nat, 0x1);
   (0x19fdec, 1%nat, 0x0);
   (0x105f00, 8%nat, 0x107e90);
   (0x107e90, 8%nat, 0x1a290);
   (0x10ba70, 8%nat, 0x0);
   (0x19fdd8, 4%nat, 0x0);
   (0x1e1d5, 8%nat, 0x612079726f6d656d);
   (0x1e1dd, 8%nat, 0x7365726464612074);
   (0x1e1e5, 4%nat, 0x70252073);
   (0x1e1e9, 1%nat, 0x0);
   (0x22730, 4%nat, 0x613e0);
   (0x104a8, 8%nat, 0xaaaaaaaaaaaaaaaa);
   (0x641378, 8%nat, 0x6413a0);
   (0x6413a8, 8%nat, 0x641b80)].

(* [comment removed for export] *)
Definition asan_annot : Z := 0x70554.
Definition both_annot : Z := 0x70fc4.
Definition as_annot (IA : as_addrs) : Z := if Z.eqb (ia_malloc IA) (ia_malloc asan_addrs) then asan_annot else both_annot.


End AsCells.
Require Stdlib.NArith.NArith Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsanAcct.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac lia ::= PuLia.lia_nd.
#[local] Ltac nia ::= PuLia.znia_nd.

Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrestrict (H : word -> bool) (m : word -> option byte)
    : word -> option byte :=
  fun a => if H a then None else m a.

(* [comment removed for export] *)
Definition munrestrict (H : word -> bool) (full m' : word -> option byte)
    : word -> option byte :=
  fun a => if H a then full a else m' a.

Definition restrict (H : word -> bool) (ms : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms;
     ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms;
     ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := mrestrict H (ms_mem ms);
     ms_rom := ms_rom ms |}.

Definition unrestrict (H : word -> bool) (full : word -> option byte)
    (ms' : machine_state) : machine_state :=
  {| ms_regs := ms_regs ms'; ms_fregs := ms_fregs ms';
     ms_pc_val := ms_pc_val ms';
     ms_svc_pending := ms_svc_pending ms';
     ms_resv := ms_resv ms'; ms_fcsr := ms_fcsr ms';
     ms_mem := munrestrict H full (ms_mem ms');
     ms_rom := ms_rom ms' |}.

(* [comment removed for export] *)
Definition H_off_segments (segs : list Segment) (H : word -> bool) : Prop :=
  forall a, H a = true -> find_segment segs (bv_unsigned a) 1 = None.

(* [comment removed for export] *)
Definition wx_segs_nowrap (segs : list Segment) : Prop :=
  forall seg, In seg segs ->
    seg_executable seg && seg_writable seg = true ->
    (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z.

(* [comment removed for export] *)
Definition woff (a : word) (k : nat) : word :=
  Z_to_bv 64 (bv_unsigned a + Z.of_nat k).

Definition range_avoids (H : word -> bool) (a : word) (n : nat) : Prop :=
  forall k, (k < n)%nat -> H (woff a k) = false.

Definition ranges_avoid (H : word -> bool) (l : list (word * nat)) : Prop :=
  forall a n, In (a, n) l -> range_avoids H a n.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma woff_0 : forall a, woff a 0 = a.
Proof.
  intros a. unfold woff. apply bv_eq. rewrite Z_to_bv_unsigned.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma woff_succ : forall a k, woff (a + 1) k = woff a (S k).
Proof.
  intros a k. unfold woff. apply bv_eq. rewrite !Z_to_bv_unsigned, bv_add_unsigned.
  assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma range_avoids_hd : forall H a n,
  range_avoids H a (S n) -> H a = false.
Proof.
  intros H a n Hr. rewrite <- (woff_0 a). apply Hr. lia.
Qed.

Lemma range_avoids_tl : forall H a n,
  range_avoids H a (S n) -> range_avoids H (a + 1) n.
Proof.
  intros H a n Hr k Hk. rewrite woff_succ. apply Hr. lia.
Qed.

Lemma range_avoids_cons : forall H a n,
  H a = false -> range_avoids H (a + 1) n -> range_avoids H a (S n).
Proof.
  intros H a n H0 Hr k Hk. destruct k as [|k].
  - rewrite woff_0. exact H0.
  - rewrite <- woff_succ. apply Hr. lia.
Qed.

Lemma ranges_avoid_nil : forall H, ranges_avoid H [].
Proof. intros H a n Hin. destruct Hin. Qed.

Lemma ranges_avoid_cons : forall H a n l,
  range_avoids H a n -> ranges_avoid H l -> ranges_avoid H ((a, n) :: l).
Proof.
  intros H a n l Ha Hl a' n' [Heq | Hin].
  - injection Heq as <- <-. exact Ha.
  - exact (Hl a' n' Hin).
Qed.

Lemma ranges_avoid_app : forall H l1 l2,
  ranges_avoid H l1 -> ranges_avoid H l2 -> ranges_avoid H (l1 ++ l2).
Proof.
  intros H l1 l2 H1 H2 a n Hin. apply in_app_or in Hin as [Hin | Hin];
    [exact (H1 a n Hin) | exact (H2 a n Hin)].
Qed.

(* [comment removed for export] *)
Lemma restrict_svc_pending : forall H ms,
  ms_svc_pending (restrict H ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.
Lemma restrict_pc : forall H ms, ms_pc (restrict H ms) = ms_pc ms.
Proof. reflexivity. Qed.





Lemma unrestrict_mem : forall H full ms,
  ms_mem (unrestrict H full ms) = munrestrict H full (ms_mem ms).
Proof. reflexivity. Qed.



Lemma munrestrict_mrestrict : forall H m,
  munrestrict H m (mrestrict H m) = m.
Proof.
  intros H m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma mrestrict_munrestrict : forall H full m,
  mrestrict H (munrestrict H full m) = mrestrict H m.
Proof.
  intros H full m. apply functional_extensionality. intro a.
  unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

Lemma unrestrict_restrict : forall H ms,
  unrestrict H (ms_mem ms) (restrict H ms) = ms.
Proof.
  intros H ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite munrestrict_mrestrict. reflexivity.
Qed.

Lemma restrict_unrestrict : forall H full ms,
  restrict H (unrestrict H full ms) = restrict H ms.
Proof.
  intros H full ms. destruct ms. unfold unrestrict, restrict. cbn.
  rewrite mrestrict_munrestrict. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hclean (H : word -> bool) (ms : machine_state) : Prop :=
  forall a, H a = true -> ms_mem ms a = None.

Lemma restrict_hclean : forall H ms, hclean H (restrict H ms).
Proof.
  intros H ms a Ha. cbn. unfold mrestrict. rewrite Ha. reflexivity.
Qed.

Lemma hclean_restrict_id : forall H ms, hclean H ms -> restrict H ms = ms.
Proof.
  intros H ms Hc. destruct ms. unfold restrict. cbn. f_equal.
  apply functional_extensionality. intro a. unfold mrestrict.
  destruct (H a) eqn:E; [symmetry; exact (Hc a E) | reflexivity].
Qed.

Lemma restrict_unrestrict_clean : forall H full ms,
  hclean H ms -> restrict H (unrestrict H full ms) = ms.
Proof.
  intros H full ms Hc. rewrite restrict_unrestrict. apply hclean_restrict_id. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section ISA.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Lemma memory_read1_hidden : forall a, H a = true -> memory_read segs a 1 = None.
Proof.
  intros a Ha. unfold memory_read. cbn [Z.of_N]. rewrite (HH a Ha). reflexivity.
Qed.

Lemma ov_read_bytes_restrict : forall n m a bs,
  ov_read_bytes segs (mrestrict H m) a n = Some bs ->
  ov_read_bytes segs m a n = Some bs /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a bs Hr.
  - cbn in Hr |- *. split; [exact Hr | intros k Hk; lia].
  - cbn [ov_read_bytes] in Hr |- *.
    unfold mrestrict in Hr at 1.
    destruct (H a) eqn:Ha.
    + rewrite (memory_read1_hidden a Ha) in Hr. discriminate.
    + destruct (match m a with
                | Some b => Some b
                | None => match memory_read segs a 1 with
                          | Some (b :: _) => Some b | _ => None end
                end) as [b|]; [|discriminate].
      destruct (ov_read_bytes segs (mrestrict H m) (a + 1) n) as [rest|] eqn:Hrest;
        [|discriminate].
      destruct (IH m (a + 1) rest Hrest) as [Hfull Hav].
      rewrite Hfull. split; [exact Hr|].
      apply range_avoids_cons; assumption.
Qed.

Lemma wview_restrict : forall m a,
  wview segs (mrestrict H m) a =
    if H a then None else wview segs m a.
Proof.
  intros m a. unfold wview, mrestrict. destruct (H a) eqn:Ha; [|reflexivity].
  rewrite (HH a Ha). reflexivity.
Qed.

Lemma store_ok_restrict : forall n m a,
  store_ok segs (mrestrict H m) a n = true ->
  store_ok segs m a n = true /\ range_avoids H a n.
Proof.
  induction n as [|n IH]; intros m a Hs.
  - split; [reflexivity | intros k Hk; lia].
  - cbn [store_ok] in Hs |- *. rewrite wview_restrict in Hs.
    destruct (H a) eqn:Ha; [discriminate|].
    destruct (wview segs m a) as [b|]; [|discriminate].
    destruct (IH m (a + 1) Hs) as [Hfull Hav].
    split; [exact Hfull | apply range_avoids_cons; assumption].
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_restrict : forall bs m a,
  range_avoids H a (length bs) ->
  write_to_mem (mrestrict H m) a bs = mrestrict H (write_to_mem m a bs).
Proof.
  induction bs as [|b bs IH]; intros m a Hav; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite <- (IH _ (a + 1) Htl). f_equal.
  apply functional_extensionality. intro x. unfold mrestrict.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha. reflexivity.
Qed.

Lemma write_to_mem_hidden : forall bs m a x,
  range_avoids H a (length bs) -> H x = true ->
  write_to_mem m a bs x = m x.
Proof.
  induction bs as [|b bs IH]; intros m a x Hav Hx; [reflexivity|].
  cbn [write_to_mem length] in *.
  pose proof (range_avoids_hd H a _ Hav) as Ha.
  pose proof (range_avoids_tl H a _ Hav) as Htl.
  rewrite (IH _ (a + 1) x Htl Hx). cbv beta.
  destruct (bv_eqb x a) eqn:Ex; [|reflexivity].
  unfold bv_eqb in Ex. apply Z.eqb_eq in Ex. apply bv_eq in Ex. subst x.
  rewrite Ha in Hx. discriminate.
Qed.

(* [comment removed for export] *)
Lemma mrestrict_visible : forall (H0 : word -> bool) m a,
  H0 a = false -> mrestrict H0 m a = m a.
Proof. intros H0 m a Ha. unfold mrestrict. rewrite Ha. reflexivity. Qed.

Lemma ov_read_bytes_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  ov_read_bytes segs (mrestrict H0 m) a n = ov_read_bytes segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [ov_read_bytes]. unfold mrestrict at 1. rewrite (range_avoids_hd H0 a n Hav).
  rewrite (IH m (a + 1) (range_avoids_tl H0 a n Hav)). reflexivity.
Qed.

Lemma rdn_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  rdn segs (mrestrict H0 m) a n = rdn segs m a n.
Proof.
  intros H0 n m a Hav. rewrite <- !ov_rdn. apply ov_read_bytes_mrestrict_eq. exact Hav.
Qed.

Lemma wview_mrestrict_eq : forall (H0 : word -> bool) m a,
  H0 a = false -> wview segs (mrestrict H0 m) a = wview segs m a.
Proof. intros H0 m a Ha. unfold wview, mrestrict. rewrite Ha. reflexivity. Qed.

Lemma store_ok_mrestrict_eq : forall (H0 : word -> bool) n m a,
  range_avoids H0 a n ->
  store_ok segs (mrestrict H0 m) a n = store_ok segs m a n.
Proof.
  intros H0. induction n as [|n IH]; intros m a Hav; [reflexivity|].
  cbn [store_ok]. rewrite (wview_mrestrict_eq H0 m a (range_avoids_hd H0 a n Hav)).
  destruct (wview segs m a); [|reflexivity].
  exact (IH m (a + 1) (range_avoids_tl H0 a n Hav)).
Qed.

(* [comment removed for export] *)

Lemma find_segment_some_spec : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
  /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.

Lemma find_segment_none_spec : forall l addr n,
  find_segment l addr n = None ->
  forall seg, In seg l ->
    ~ ((Z.of_N (seg_base seg) <= addr)%Z
       /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
Lemma in_segment_not_hidden : forall (x : word) seg,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned x)%Z ->
  (bv_unsigned x + 1 <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  H x = false.
Proof.
  intros x seg Hin H1 H2. destruct (H x) eqn:Hx; [|reflexivity].
  exfalso. exact (find_segment_none_spec segs (bv_unsigned x) 1 (HH x Hx) seg Hin (conj H1 H2)).
Qed.

Lemma seg_ov_read_bytes_restrict : forall n m seg a,
  In seg segs ->
  (Z.of_N (seg_base seg) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z ->
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= 2 ^ 64)%Z ->
  seg_ov_read_bytes (mrestrict H m) seg a n = seg_ov_read_bytes m seg a n.
Proof.
  induction n as [|n IH]; intros m seg a Hin Hlo Hhi Htop; [reflexivity|].
  cbn [seg_ov_read_bytes].
  assert (Ha : H a = false) by (apply (in_segment_not_hidden a seg Hin); lia).
  unfold mrestrict at 1. rewrite Ha.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z).
    { rewrite bv_add_unsigned.
      assert (H1 : bv_unsigned (1 : word) = 1%Z) by reflexivity. rewrite H1.
      apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64)%Z.
      pose proof (bv_unsigned_in_range 64 a). lia. }
    rewrite (IH m seg (a + 1) Hin) by lia. reflexivity.
Qed.

Lemma code_read_ov_restrict : forall m a n,
  code_read_ov segs (mrestrict H m) a n = code_read_ov segs m a n.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf; [|reflexivity].
  destruct (seg_executable seg && seg_writable seg) eqn:Ewx; [|reflexivity].
  destruct (find_segment_some_spec segs _ _ seg Hf) as (Hin & H1 & H2).
  apply seg_ov_read_bytes_restrict; [exact Hin | exact H1 | | exact (Hwx seg Hin Ewx)].
  rewrite N_nat_Z. exact H2.
Qed.

Lemma fetch_word_ov_restrict : forall m a,
  fetch_word_ov segs (mrestrict H m) a = fetch_word_ov segs m a.
Proof. intros m a. unfold fetch_word_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_ov_restrict : forall m a,
  fetch_half_ov segs (mrestrict H m) a = fetch_half_ov segs m a.
Proof. intros m a. unfold fetch_half_ov. rewrite code_read_ov_restrict. reflexivity. Qed.

Lemma fetch_half_any_restrict : forall m a,
  fetch_half_any segs (mrestrict H m) a = fetch_half_any segs m a.
Proof. intros m a. unfold fetch_half_any. rewrite fetch_half_ov_restrict. reflexivity. Qed.

Lemma fetch_tail_any_restrict : forall m a,
  fetch_tail_any segs (mrestrict H m) a = fetch_tail_any segs m a.
Proof. intros m a. unfold fetch_tail_any. rewrite !fetch_half_any_restrict. reflexivity. Qed.

Lemma fetch_failure_restrict : forall m a,
  fetch_failure segs (mrestrict H m) a = fetch_failure segs m a.
Proof. intros m a. unfold fetch_failure. rewrite fetch_half_any_restrict. reflexivity. Qed.

(* [comment removed for export] *)
Lemma interp_eff_accesses_restrict : forall t m c mr' rs,
  interp_eff_accesses segs t (mrestrict H m)
    = MachineOk (@mkAccessReport _ (c, mr') rs) ->
  exists mf',
    interp_eff_accesses segs t m = MachineOk (@mkAccessReport _ (c, mf') rs)
    /\ mr' = mrestrict H mf'
    /\ (forall x, H x = true -> mf' x = m x)
    /\ ranges_avoid H rs.
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH]; (* [comment removed for export] *)
    intros m c mr' rs Hi; cbn [interp_eff_accesses] in Hi |- *;
    try discriminate.
  - (* [comment removed for export] *)
    injection Hi as <- <- <-. exists m.
    split; [reflexivity|]. split; [reflexivity|]. split; [intros; reflexivity|].
    apply ranges_avoid_nil.
  - (* [comment removed for export] *)
    destruct (ov_read_bytes segs (mrestrict H m) a (width_bytes n)) as [bs|] eqn:Hrd;
      [|discriminate].
    destruct (ov_read_bytes_restrict _ m a bs Hrd) as [Hfull Hav].
    rewrite Hfull.
    destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) (mrestrict H m))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ m c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split; [exact Hhid|].
    apply ranges_avoid_cons; assumption.
  - (* [comment removed for export] *)
    destruct (store_ok segs (mrestrict H m) a (width_bytes n)) eqn:Hso; [|discriminate].
    destruct (store_ok_restrict _ m a Hso) as [Hfull Hav]. rewrite Hfull.
    assert (Hlen : length (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) = width_bytes n)
      by apply length_Z_to_le_bytes.
    rewrite (write_to_mem_restrict (Z_to_le_bytes (width_bytes n) (bv_unsigned v)) m a)
      in Hi by (rewrite Hlen; exact Hav).
    destruct (interp_eff_accesses segs k
                (mrestrict H (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))))
      as [[[c1 m1] rs1]| |] eqn:Hk; try discriminate.
    cbn [access_value accessed_ranges] in Hi. injection Hi as <- <- <-.
    destruct (IH _ c1 m1 rs1 Hk) as (mf' & Hint & Hmr & Hhid & Hrs).
    rewrite Hint. cbn [access_value accessed_ranges].
    exists mf'. split; [reflexivity|]. split; [exact Hmr|]. split.
    + intros x Hx. rewrite (Hhid x Hx).
      apply (write_to_mem_hidden _ m a x); [rewrite Hlen; exact Hav | exact Hx].
    + apply ranges_avoid_cons; assumption.
Qed.

(* [comment removed for export] *)
Lemma decode_exec_accesses_restrict : forall ms w msr' rs',
  decode_exec_accesses segs (restrict H ms) w
    = MachineOk (@mkAccessReport _ msr' rs') ->
  decode_exec_accesses segs ms w
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms w msr' rs' Hd. unfold decode_exec_accesses in Hd |- *.
  destruct (is_ecall w) eqn:Hec.
  - injection Hd as <- <-.
    split; [|split; [apply ranges_avoid_nil | apply (restrict_hclean H ms)]].
    unfold unrestrict, restrict. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending].
    rewrite munrestrict_mrestrict. destruct ms; reflexivity.
  - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom restrict] in Hd.
    destruct (interp_eff_accesses segs
                (exec (Z_to_bv 64 isz) i
                   {| c_regs := ms_regs ms; c_fregs := ms_fregs ms;
                      c_pc := ms_pc_val ms; c_fcsr := ms_fcsr ms;
                      c_resv := ms_resv ms |})
                (mrestrict H (ms_mem ms)))
      as [[[c1 m1] rs1]| |] eqn:Hint; try discriminate.
    cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-.
    destruct (interp_eff_accesses_restrict _ _ c1 m1 rs1 Hint)
      as (mf' & Hfull & -> & Hhid & Hrs).
    rewrite Hfull. cbn [access_value accessed_ranges].
    split; [|split; [exact Hrs|]].
    + unfold unrestrict. cbn.
      replace (munrestrict H (ms_mem ms) (mrestrict H mf')) with mf'; [reflexivity|].
      apply functional_extensionality. intro x. unfold munrestrict, mrestrict.
      destruct (H x) eqn:Hx; [exact (Hhid x Hx) | reflexivity].
    + intros x Hx. cbn. unfold mrestrict. rewrite Hx. reflexivity.
Qed.

Theorem step_accesses_restrict : forall ms msr' rs',
  step_accesses segs (restrict H ms) = MachineOk (@mkAccessReport _ msr' rs') ->
  step_accesses segs ms
    = MachineOk (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs')
  /\ ranges_avoid H rs'
  /\ hclean H msr'.
Proof.
  intros ms msr' rs' Hs. unfold step_accesses in Hs |- *.
  rewrite restrict_pc in Hs. cbn [ms_mem restrict] in Hs.
  rewrite fetch_word_ov_restrict, fetch_tail_any_restrict, fetch_failure_restrict in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|].
  { exact (decode_exec_accesses_restrict ms w msr' rs' Hs). }
  exfalso. unfold fetch_failure in Hs.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

(* [comment removed for export] *)
Theorem step_restrict_sound : forall ms msr',
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists rep,
    step_accesses segs ms = MachineOk rep
    /\ access_value _ rep = unrestrict H (ms_mem ms) msr'
    /\ ranges_avoid H (accessed_ranges _ rep)
    /\ hclean H msr'
    /\ restrict H (unrestrict H (ms_mem ms) msr') = msr'.
Proof.
  intros ms msr' Hs. unfold RiscvSemantics.step, drop_access_report in Hs.
  destruct (step_accesses segs (restrict H ms)) as [[v rs]| |] eqn:Hsa; try discriminate.
  injection Hs as ->.
  destruct (step_accesses_restrict ms msr' rs Hsa) as (Hfull & Hrs & Hcl).
  exists (@mkAccessReport _ (unrestrict H (ms_mem ms) msr') rs).
  split; [exact Hfull|]. split; [reflexivity|]. split; [exact Hrs|]. split; [exact Hcl|].
  apply restrict_unrestrict_clean. exact Hcl.
Qed.


(* [comment removed for export] *)
Lemma step_accesses_ecall_shape : forall ms msr' rs',
  step_accesses segs ms = MachineOk (@mkAccessReport _ msr' rs') ->
  ms_svc_pending msr' <> None ->
  rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
  /\ ms_svc_pending msr' = Some (ms_reg ms 17).
Proof.
  intros ms msr' rs' Hs Hsvc.
  assert (Hdec : forall w, decode_exec_accesses segs ms w = MachineOk (@mkAccessReport _ msr' rs') ->
            rs' = [] /\ ms_mem msr' = ms_mem ms /\ ms_regs msr' = ms_regs ms
            /\ ms_svc_pending msr' = Some (ms_reg ms 17)).
  { intros w Hd. unfold decode_exec_accesses in Hd.
    destruct (is_ecall w).
    - injection Hd as <- <-. cbn. repeat split; reflexivity.
    - destruct (decode_any w) as [[i isz]|]; [|destruct (is_defined_illegal w); discriminate].
      destruct (interp_eff_accesses segs _ _) as [[[c1 m1] rs1]| |]; try discriminate.
      cbn [access_value accessed_ranges] in Hd. injection Hd as <- <-. cbn in Hsvc.
      exfalso. apply Hsvc. reflexivity. }
  unfold step_accesses in Hs.
  destruct (fetch_word segs (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_word_ov segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|]; [exact (Hdec w Hs)|].
  exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Hf; try discriminate.
  unfold fetch_failure in Hf.
  destruct (negb (bv_unsigned (ms_pc ms) mod 2 =? 0)%Z); [discriminate|].
  destruct (fetch_byte_traps segs (ms_pc ms) || fetch_byte_traps segs (ms_pc ms + 1)
            || match fetch_half_any segs (ms_mem ms) (ms_pc ms) with
               | Some _ => fetch_byte_traps segs (ms_pc ms + 2) || fetch_byte_traps segs (ms_pc ms + 3)
               | None => false end); discriminate.
Qed.

End ISA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition page_allowedb (A : list (Z * Z)) (p : word) : bool :=
  existsb (fun iv => (fst iv <=? bv_unsigned p)%Z
                     && (bv_unsigned p + page_size <=? snd iv)%Z) A.

(* [comment removed for export] *)
Definition A_wf (A : list (Z * Z)) : Prop :=
  Forall (fun iv => (fst iv <= snd iv)%Z /\ (fst iv) mod page_size = 0
                    /\ (snd iv) mod page_size = 0)%Z A.

(* [comment removed for export] *)
Fixpoint A_bytes (A : list (Z * Z)) : Z :=
  match A with
  | [] => 0
  | iv :: r => (snd iv - fst iv) + A_bytes r
  end%Z.

(* [comment removed for export] *)
Definition lazy_cover (H : word -> bool) (lazy : list (word * word))
    (A : list (Z * Z)) : Prop :=
  forall w : word,
    page_in_ranges (page_base w) lazy = true -> H w = false ->
    page_allowedb A (page_base w) = true.

(* [comment removed for export] *)
Definition eager_used (m : Model) : Z :=
  live_bytes (maps_subtract_all (vm_backed_maps (m_vmmaps m)) (m_vm_lazy m)).

Lemma vm_backing_used_split : forall m,
  vm_backing_used m
  = (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Record MInv (A : list (Z * Z)) (m : Model) : Prop := mkMInv {
  minv_nodup    : List.NoDup (m_vm_materialized m);
  minv_aligned  : forall p, In p (m_vm_materialized m) ->
                    (bv_unsigned p mod page_size = 0)%Z;
  minv_allowed  : forall p, In p (m_vm_materialized m) -> page_allowedb A p = true;
  minv_lazy     : forall p, In p (m_vm_materialized m) ->
                    page_in_ranges p (m_vm_lazy m) = true;
  minv_budget   : (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z
}.

(* [comment removed for export] *)
Definition same_but_materialized (m m' : Model) : Prop :=
  m' = with_vm_backing (m_vm_lazy m) (m_vm_materialized m') m.

Lemma same_but_materialized_refl : forall m, same_but_materialized m m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma same_but_materialized_trans : forall m1 m2 m3,
  same_but_materialized m1 m2 -> same_but_materialized m2 m3 ->
  same_but_materialized m1 m3.
Proof.
  unfold same_but_materialized. intros m1 m2 m3 -> ->.
  destruct m1 as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma with_vm_backing_same : forall m mat',
  same_but_materialized m (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros [fd [maps lazy mat] io fs proc lim tm] mat'. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma same_but_materialized_frame : forall m m',
  same_but_materialized m m' ->
  m_fd m' = m_fd m /\ m_vmmaps m' = m_vmmaps m /\ m_vm_lazy m' = m_vm_lazy m
  /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m  (* [comment removed for export] *)
  /\ m_fds m' = m_fds m /\ m_pipes m' = m_pipes m /\ m_stdin m' = m_stdin m
  /\ m_fs m' = m_fs m /\ m_halted m' = m_halted m /\ m_tid m' = m_tid m
  /\ m_rlimit_core m' = m_rlimit_core m /\ m_clock m' = m_clock m
  /\ eager_used m' = eager_used m.
Proof.
  intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm].
  repeat split; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint A_pages (A : list (Z * Z)) : list Z :=
  match A with
  | [] => []
  | iv :: r =>
      map (fun i => (fst iv + page_size * Z.of_nat i)%Z)
          (seq 0 (Z.to_nat ((snd iv - fst iv) / page_size)))
      ++ A_pages r
  end.

Lemma Zmod0_multiple : forall a, (a mod page_size = 0)%Z -> exists q, a = (page_size * q)%Z.
Proof.
  intros a Ha. exists (a / page_size)%Z.
  pose proof (Z.div_mod a page_size ltac:(unfold page_size; lia)) as Hdm.
  rewrite Ha, Z.add_0_r in Hdm. exact Hdm.
Qed.

Lemma A_pages_length : forall A,
  A_wf A -> (Z.of_nat (length (A_pages A)) * page_size = A_bytes A)%Z.
Proof.
  induction A as [|[lo hi] A IH]; intros Hwf; [reflexivity|].
  cbn [A_pages A_bytes fst snd]. inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst.
  cbn [fst snd] in *.
  rewrite length_app, length_map, length_seq, Nat2Z.inj_add, Z.mul_add_distr_r.
  rewrite (IH Hwf').
  destruct (Zmod0_multiple lo Hlo) as [qlo ->].
  destruct (Zmod0_multiple hi Hhi) as [qhi ->].
  replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
  rewrite Z.div_mul by (unfold page_size; lia).
  rewrite Z2Nat.id by (unfold page_size in Hle; lia).
  reflexivity.
Qed.

Lemma A_pages_in : forall A p,
  A_wf A ->
  (bv_unsigned p mod page_size = 0)%Z ->
  page_allowedb A p = true ->
  In (bv_unsigned p) (A_pages A).
Proof.
  induction A as [|[lo hi] A IH]; intros p Hwf Hal Hpa; [discriminate|].
  inversion Hwf as [|x l [Hle [Hlo Hhi]] Hwf']; subst. cbn [fst snd] in *.
  cbn [A_pages fst snd]. apply in_or_app.
  unfold page_allowedb in Hpa. cbn [existsb fst snd] in Hpa.
  apply orb_true_iff in Hpa as [Hpa | Hpa].
  - left. apply andb_true_iff in Hpa as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (Zmod0_multiple lo Hlo) as [qlo Eqlo].
    destruct (Zmod0_multiple hi Hhi) as [qhi Eqhi].
    destruct (Zmod0_multiple (bv_unsigned p) Hal) as [qp Eqp].
    rewrite Eqp in *. rewrite Eqlo, Eqhi in *.
    replace (page_size * qhi - page_size * qlo)%Z with ((qhi - qlo) * page_size)%Z by lia.
    rewrite Z.div_mul by (unfold page_size; lia).
    apply in_map_iff. exists (Z.to_nat (qp - qlo)).
    unfold page_size in *.
    split.
    + rewrite Z2Nat.id by lia. lia.
    + apply in_seq. lia.
  - right. apply IH; [exact Hwf' | exact Hal | exact Hpa].
Qed.

Lemma NoDup_map_bv_unsigned : forall (l : list word),
  List.NoDup l -> List.NoDup (map bv_unsigned l).
Proof.
  intros l Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor; [|exact IH].
  intros Hin. apply in_map_iff in Hin as (y & Hy & Hiny).
  apply bv_eq in Hy. subst y. exact (Hx Hiny).
Qed.

Theorem allowed_pages_bound : forall A (pages : list word),
  A_wf A ->
  List.NoDup pages ->
  (forall p, In p pages -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p pages -> page_allowedb A p = true) ->
  (Z.of_nat (length pages) * page_size <= A_bytes A)%Z.
Proof.
  intros A pages Hwf Hnd Hal Hpa.
  rewrite <- (A_pages_length A Hwf).
  assert (Hlen : (length pages <= length (A_pages A))%nat).
  { rewrite <- (length_map bv_unsigned pages).
    apply NoDup_incl_length.
    - apply NoDup_map_bv_unsigned. exact Hnd.
    - intros z Hz. apply in_map_iff in Hz as (p & <- & Hp).
      apply A_pages_in; [exact Hwf | exact (Hal p Hp) | exact (Hpa p Hp)]. }
  unfold page_size. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma two64_as_pages : (2 ^ 64 = page_size * 2 ^ 52)%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma page_base_woff : forall a k,
  page_base (woff a k) = page_base_of (bv_unsigned a + Z.of_nat k).
Proof.
  intros a k. unfold page_base, woff, page_base_of.
  set (z := (bv_unsigned a + Z.of_nat k)%Z).
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  assert (Hz : (0 <= z)%Z) by (unfold z; lia).
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite !two64_as_pages.
  set (r := (z mod (page_size * 2 ^ 52))%Z).
  assert (Hps : (0 < page_size)%Z) by (unfold page_size; lia).
  (* [comment removed for export] *)
  pose proof (Z.div_mod z (page_size * 2 ^ 52) ltac:(lia)) as Hdm.
  fold r in Hdm.
  set (q := (z / (page_size * 2 ^ 52))%Z) in Hdm.
  assert (Hfl : (z / page_size * page_size = page_size * 2 ^ 52 * q + r / page_size * page_size)%Z).
  { rewrite Hdm at 1.
    replace (page_size * 2 ^ 52 * q + r)%Z with (r + (2 ^ 52 * q) * page_size)%Z by lia.
    rewrite Z.div_add by lia. lia. }
  rewrite Hfl.
  replace (page_size * 2 ^ 52 * q + r / page_size * page_size)%Z
    with (r / page_size * page_size + q * (page_size * 2 ^ 52))%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma page_base_of_aligned : forall z,
  (bv_unsigned (page_base_of z) mod page_size = 0)%Z.
Proof.
  intros z. unfold page_base_of. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64)%Z. rewrite two64_as_pages.
  rewrite (Z.mul_comm (z / page_size) page_size).
  rewrite Zmult_mod_distr_l.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma page_insert_nodup : forall p pages,
  List.NoDup pages -> List.NoDup (page_insert p pages).
Proof.
  intros p pages Hnd. unfold page_insert.
  destruct (page_mem p pages) eqn:Hm; [exact Hnd|].
  constructor; [|exact Hnd].
  intros Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma page_mem_false_not_in : forall p pages,
  page_mem p pages = false -> ~ In p pages.
Proof.
  intros p pages Hm Hin. unfold page_mem in Hm.
  assert (Ht : existsb (bv_eqb p) pages = true).
  { apply existsb_exists. exists p. split; [exact Hin|]. unfold bv_eqb. apply Z.eqb_refl. }
  rewrite Ht in Hm. discriminate.
Qed.

Lemma access_pages_acc_nodup : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; intros base pages Hnd; cbn [access_pages_acc]; [exact Hnd|].
  apply IH. apply page_insert_nodup. exact Hnd.
Qed.

Lemma accesses_pages_nodup : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; intros pages Hnd; cbn [accesses_pages]; [exact Hnd|].
  apply IH. apply access_pages_acc_nodup. exact Hnd.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages Hin. unfold page_insert in Hin.
  destruct (page_mem q pages); [right; exact Hin|].
  destruct Hin as [Hqp | Hin]; [left; symmetry; exact Hqp | right; exact Hin].
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages
  \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k)%Z.
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p Hin.
  - left; exact Hin.
  - destruct (IH (base + 1)%Z _ p Hin) as [Hin' | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin') as [-> | Hin''].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin''.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\
                   p = page_base_of (bv_unsigned a + Z.of_nat k)%Z.
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p Hin.
  - left; exact Hin.
  - destruct (IH _ p Hin) as [Hin' | (a' & n' & k & Hin' & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin') as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin' | split; assumption].
Qed.

(* [comment removed for export] *)
Lemma new_pages_props : forall H A lazy mat ranges,
  lazy_cover H lazy A ->
  ranges_avoid H ranges ->
  let new := newly_materialized_pages lazy mat ranges in
  List.NoDup new
  /\ (forall p, In p new -> ~ In p mat)
  /\ (forall p, In p new -> (bv_unsigned p mod page_size = 0)%Z)
  /\ (forall p, In p new -> page_in_ranges p lazy = true)
  /\ (forall p, In p new -> page_allowedb A p = true).
Proof.
  intros H A lazy mat ranges Hcov Hav new.
  assert (Hchar : forall p, In p new ->
            page_in_ranges p lazy = true /\ page_mem p mat = false
            /\ exists a n k, In (a, n) ranges /\ (k < n)%nat
                             /\ p = page_base_of (bv_unsigned a + Z.of_nat k)%Z).
  { intros p Hin. unfold new, newly_materialized_pages in Hin.
    apply filter_In in Hin as [Hin Hf]. apply andb_true_iff in Hf as [Hl Hm].
    split; [exact Hl|]. split; [destruct (page_mem p mat); [discriminate | reflexivity]|].
    destruct (accesses_pages_in ranges [] p Hin) as [[] | Hex]. exact Hex. }
  split; [|split; [|split; [|split]]].
  - unfold new, newly_materialized_pages. apply NoDup_filter.
    apply accesses_pages_nodup. constructor.
  - intros p Hp. destruct (Hchar p Hp) as (_ & Hm & _). apply page_mem_false_not_in. exact Hm.
  - intros p Hp. destruct (Hchar p Hp) as (_ & _ & a & n & k & _ & _ & ->).
    apply page_base_of_aligned.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _). exact Hl.
  - intros p Hp. destruct (Hchar p Hp) as (Hl & _ & a & n & k & Hin & Hk & Ep).
    pose proof (Hav a n Hin k Hk) as Hw.
    rewrite <- page_base_woff in Ep. rewrite Ep in Hl |- *.
    exact (Hcov (woff a k) Hl Hw).
Qed.

(* [comment removed for export] *)
Lemma m_vm_materialized_wvb : forall l X m,
  m_vm_materialized (with_vm_backing l X m) = X.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_wvb : forall l X m, m_vm_lazy (with_vm_backing l X m) = l.
Proof. reflexivity. Qed.
Lemma m_vmmaps_wvb : forall l X m, m_vmmaps (with_vm_backing l X m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma eager_used_wvb : forall X m,
  eager_used (with_vm_backing (m_vm_lazy m) X m) = eager_used m.
Proof. reflexivity. Qed.

Lemma with_vm_backing_id : forall m,
  with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Lemma MInv_wvb : forall A m X,
  List.NoDup X ->
  (forall p, In p X -> (bv_unsigned p mod page_size = 0)%Z) ->
  (forall p, In p X -> page_allowedb A p = true) ->
  (forall p, In p X -> page_in_ranges p (m_vm_lazy m) = true) ->
  (eager_used m + A_bytes A <= vm_limit (m_vmmaps m))%Z ->
  MInv A (with_vm_backing (m_vm_lazy m) X m).
Proof.
  intros A m X H1 H2 H3 H4 H5. constructor;
    rewrite ?m_vm_materialized_wvb, ?m_vm_lazy_wvb, ?m_vmmaps_wvb, ?eager_used_wvb;
    assumption.
Qed.

(* [comment removed for export] *)
Theorem materialize_restricted : forall H A m ranges,
  lazy_cover H (m_vm_lazy m) A ->
  A_wf A ->
  MInv A m ->
  ranges_avoid H ranges ->
  exists mat',
    materialize_model_accesses m ranges
      = Some (with_vm_backing (m_vm_lazy m) mat' m)
    /\ MInv A (with_vm_backing (m_vm_lazy m) mat' m).
Proof.
  intros H A m ranges Hcov Hwf [Hnd Hal Hpa Hlz Hbud] Hav.
  destruct (new_pages_props H A (m_vm_lazy m) (m_vm_materialized m) ranges Hcov Hav)
    as (Nnd & Nfresh & Nal & Nlz & Npa).
  unfold materialize_model_accesses, materialize_accesses.
  set (new := newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) ranges) in *.
  assert (Happ_nd : List.NoDup (new ++ m_vm_materialized m)).
  { apply NoDup_app; [exact Nnd | exact Hnd | exact Nfresh]. }
  assert (Happ_al : forall p, In p (new ++ m_vm_materialized m) ->
                      (bv_unsigned p mod page_size = 0)%Z).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nal p Hp) | exact (Hal p Hp)]. }
  assert (Happ_pa : forall p, In p (new ++ m_vm_materialized m) -> page_allowedb A p = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Npa p Hp) | exact (Hpa p Hp)]. }
  assert (Happ_lz : forall p, In p (new ++ m_vm_materialized m) ->
                      page_in_ranges p (m_vm_lazy m) = true).
  { intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (Nlz p Hp) | exact (Hlz p Hp)]. }
  pose proof (allowed_pages_bound A (new ++ m_vm_materialized m) Hwf Happ_nd Happ_al Happ_pa)
    as Hbound.
  rewrite length_app, Nat2Z.inj_add in Hbound.
  destruct new as [|p0 new'] eqn:Enew.
  - exists (m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
  - rewrite vm_backing_used_split.
    replace (eager_used m + Z.of_nat (length (m_vm_materialized m)) * page_size
             + Z.of_nat (length (p0 :: new')) * page_size
             <=? vm_limit (m_vmmaps m))%Z with true.
    2:{ symmetry. apply Z.leb_le. unfold page_size in *. lia. }
    exists ((p0 :: new') ++ m_vm_materialized m). split; [reflexivity|].
    apply MInv_wvb; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Nodes.
Variable segs : list Segment.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

(* [comment removed for export] *)
Definition node_ok (c : config) (I : Type)
    (evs : I -> list event) (nx : I -> config) : Prop :=
  (forall i, sstep_cfg segs CfgStep.kit_cfg c (evs i) (SNext (nx i)))
  /\ (forall e st, sstep_cfg segs CfgStep.kit_cfg c e st -> exists i, e = evs i /\ st = SNext (nx i)).

(* [comment removed for export] *)
Theorem mi_account_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists mat',
    mi_account_step segs ms model
      = MachineOk (unrestrict H (ms_mem ms) msr',
                   with_vm_backing (m_vm_lazy model) mat' model)
    /\ MInv A (with_vm_backing (m_vm_lazy model) mat' model)
    /\ hclean H msr'.
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hs.
  destruct (step_restrict_sound segs H HH Hwx ms msr' Hs) as (rep & Hsa & Hv & Hrs & Hcl & _).
  destruct (materialize_restricted H A model (accessed_ranges _ rep) Hcov Hwf Hinv Hrs)
    as (mat' & Hmat & Hinv').
  exists mat'. unfold mi_account_step. rewrite Hsa, Hmat, Hv.
  split; [reflexivity | split; [exact Hinv' | exact Hcl]].
Qed.

(* [comment removed for export] *)
Lemma sstep_instr_det : forall ms model ms1 model1 e st,
  ms_svc_pending ms = None ->
  mi_account_step segs ms model = MachineOk (ms1, model1) ->
  sstep segs (mkCfg ms model) e st ->
  e = [] /\ st = SNext (mkCfg ms1 model1).
Proof.
  intros ms model ms1 model1 e st Hsvc Hacc Hss.
  inversion Hss; subst;
    match goal with
    | Hp : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in Hp; discriminate
    | Ha : mi_account_step segs ms model = _ |- _ =>
        rewrite Hacc in Ha; try discriminate; injection Ha as <- <-; split; reflexivity
    end.
Qed.

(* [comment removed for export] *)
Theorem node_instr_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  exists model',
    MInv A model' /\ same_but_materialized model model'
    /\ hclean H msr'
    /\ mi_account_step segs ms model
         = MachineOk (unrestrict H (ms_mem ms) msr', model')
    /\ node_ok (mkCfg ms model) unit (fun _ => [])
               (fun _ => mkCfg (unrestrict H (ms_mem ms) msr') model').
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs.
  destruct (mi_account_step_restricted A ms msr' model Hcov Hwf Hinv Hs)
    as (mat' & Hacc & Hinv' & Hcl).
  exists (with_vm_backing (m_vm_lazy model) mat' model).
  split; [exact Hinv'|]. split; [apply with_vm_backing_same|]. split; [exact Hcl|].
  split; [exact Hacc|].
  apply (CfgStep.node_transfer_on segs CfgStep.kit_cfg); [CfgStep.kit_pending_on |].
  split.
  - intros []. apply sstep_instr; [exact Hh | exact Hsvc | exact Hacc].
  - intros e st Hss. exists tt.
    exact (sstep_instr_det ms model _ _ e st Hsvc Hacc Hss).
Qed.

(* [comment removed for export] *)
Lemma step_hclean : forall ms ms',
  hclean H ms ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  hclean H ms'.
Proof.
  intros ms ms' Hc Hs. rewrite <- (hclean_restrict_id H ms Hc) in Hs.
  destruct (step_restrict_sound segs H HH Hwx ms ms' Hs) as (rep & _ & _ & _ & Hcl & _).
  exact Hcl.
Qed.

Lemma msteps_hclean : forall ms ms',
  msteps segs ms ms' -> hclean H ms -> hclean H ms'.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hrest IH]; intros Hc.
  - exact Hc.
  - apply IH. exact (step_hclean ms ms1 Hc Hstep).
Qed.

Lemma unrestrict_munrestrict : forall f g ms',
  unrestrict H (munrestrict H f g) ms' = unrestrict H f ms'.
Proof.
  intros f g ms'. unfold unrestrict. f_equal.
  apply functional_extensionality. intro x. unfold munrestrict.
  destruct (H x); reflexivity.
Qed.

(* [comment removed for export] *)
Variable P : config -> Prop.
Hypothesis P_silent1 : forall c c',
  node_ok c unit (fun _ => []) (fun _ => c') -> P c' -> P c.

Theorem rz_step_restricted : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs (restrict H ms) = MachineOk msr' ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs Hk.
  destruct (node_instr_restricted A ms msr' model Hcov Hwf Hinv Hh Hsvc Hs)
    as (model' & Hinv' & Hsame & _ & _ & Hnode).
  exact (P_silent1 _ _ Hnode (Hk model' Hinv' Hsame)).
Qed.

Theorem rz_msteps_restricted : forall A msr0 msr',
  msteps segs msr0 msr' ->
  forall ms model,
  msr0 = restrict H ms ->
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  (forall model', MInv A model' -> same_but_materialized model model' ->
                  P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A msr0 msr' Hms.
  induction Hms as [msr | msr msr1 msr2 Hsvc Hstep Hrest IH];
    intros ms model -> Hcov Hwf Hinv Hh Hk.
  - specialize (Hk model Hinv (same_but_materialized_refl model)).
    rewrite unrestrict_restrict in Hk. exact Hk.
  - rewrite restrict_svc_pending in Hsvc.
    destruct (node_instr_restricted A ms msr1 model Hcov Hwf Hinv Hh Hsvc Hstep)
      as (model1 & Hinv1 & Hsame1 & Hcl1 & _ & Hnode).
    apply (P_silent1 _ _ Hnode).
    pose proof (same_but_materialized_frame model model1 Hsame1) as Hfr.
    apply (IH (unrestrict H (ms_mem ms) msr1) model1).
    + symmetry. apply restrict_unrestrict_clean. exact Hcl1.
    + replace (m_vm_lazy model1) with (m_vm_lazy model) by (symmetry; apply Hfr). exact Hcov.
    + exact Hwf.
    + exact Hinv1.
    + replace (m_halted model1) with (m_halted model) by (symmetry; apply Hfr). exact Hh.
    + intros model' Hinv' Hsame'.
      rewrite unrestrict_mem, unrestrict_munrestrict.
      apply Hk; [exact Hinv' | exact (same_but_materialized_trans _ _ _ Hsame1 Hsame')].
Qed.
(* [comment removed for export] *)
Theorem rz_msteps_restricted' : forall A ms msr' model,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      P (mkCfg (unrestrict H (ms_mem ms) msr') model')) ->
  P (mkCfg ms model).
Proof.
  intros A ms msr' model Hcov Hwf Hinv Hh Hms Hk.
  pose proof (msteps_hclean _ _ Hms (restrict_hclean H ms)) as Hcl.
  apply (rz_msteps_restricted A (restrict H ms) msr' Hms ms model eq_refl Hcov Hwf Hinv Hh).
  intros model' Hinv' Hsame'. exact (Hk model' Hinv' Hsame' Hcl).
Qed.

End Nodes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma materialize_model_accesses_nil : forall m,
  materialize_model_accesses m [] = Some m.
Proof.
  intros m. unfold materialize_model_accesses, materialize_accesses.
  unfold newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite with_vm_backing_id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition materialized_succ (m : Model) (accs : list (word * nat)) : Model :=
  match materialize_model_accesses m accs with
  | Some m' => m'
  | None => m
  end.

Section SyscallNode.
Variable segs : list Segment.
Variable H : word -> bool.

(* [comment removed for export] *)
Theorem node_syscall_restricted :
  forall A ms model x8 (I : Type)
         (eff : I -> SyscallEffect) (mdl : I -> Model) (evs : I -> list event),
  A_wf A ->
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (eff i) (mdl i) (evs i))) ->
  (forall r, syscall_spec (sys_input segs ms x8) model r ->
             exists i, r = Ok (eff i) (mdl i) (evs i)) ->
  (forall i, m_halted (mdl i) = None) ->
  (forall i, lazy_cover H (m_vm_lazy (mdl i)) A) ->
  (forall i, MInv A (mdl i)) ->
  (forall i, ranges_avoid H (syscall_effect_accesses (eff i))) ->
  (forall i, MInv A (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))
             /\ same_but_materialized (mdl i)
                  (materialized_succ (mdl i) (syscall_effect_accesses (eff i))))
  /\ node_ok segs (mkCfg ms model) I evs
       (fun i => mkCfg (advance_past_svc (apply_effect ms (eff i)))
                       (materialized_succ (mdl i) (syscall_effect_accesses (eff i)))).
Proof.
  intros A ms model x8 I eff mdl evs Hwf Hh Hsvc Hnalloc Hsound Hcompl Hnh Hcov Hinv Hav.
  assert (Hmat : forall i, exists mat',
            materialize_model_accesses (mdl i) (syscall_effect_accesses (eff i))
              = Some (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))
            /\ MInv A (with_vm_backing (m_vm_lazy (mdl i)) mat' (mdl i))).
  { intros i. exact (materialize_restricted H A (mdl i) _ (Hcov i) Hwf (Hinv i) (Hav i)). }
  split.
  - intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
    unfold materialized_succ. rewrite Hm. split; [exact Hinv' | apply with_vm_backing_same].
  - apply (CfgStep.node_transfer_on segs CfgStep.kit_cfg);
      [exact (CfgStep.kit_pending_on_sysno segs ms model x8 _ Hsvc eq_refl Hnalloc) |].
    split.
    + intros i. destruct (Hmat i) as (mat' & Hm & Hinv').
      unfold materialized_succ. rewrite Hm.
      eapply sstep_syscall; [exact Hh | exact Hsvc | exact (Hsound i) | exact (Hnh i) | exact Hm].
    + intros e st Hss. inversion Hss; subst;
        match goal with
        | Hp : ms_svc_pending ms = None |- _ => rewrite Hsvc in Hp; discriminate
        | Hp : ms_svc_pending ms = Some ?x |- _ =>
            rewrite Hsvc in Hp; injection Hp as <-
        end;
        match goal with
        | Hsp : syscall_spec _ _ ?r |- _ =>
            destruct (Hcompl _ Hsp) as [i Ei]; try discriminate Ei;
            injection Ei as -> -> ->
        end.
      * (* [comment removed for export] *)
        exists i. split; [reflexivity|].
        unfold materialized_succ.
        match goal with Hm : materialize_model_accesses _ _ = Some _ |- _ => rewrite Hm end.
        reflexivity.
      * (* [comment removed for export] *)
        destruct (Hmat i) as (mat' & Hm & _).
        match goal with Hn : materialize_model_accesses _ _ = None |- _ => rewrite Hm in Hn; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hc : m_halted (mdl i) = Some _ |- _ => rewrite (Hnh i) in Hc; discriminate end.
      * (* [comment removed for export] *)
        match goal with Hk : m_killed (mdl i) = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh i)) in Hk; discriminate end.
Qed.
End SyscallNode.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkH (L : list (word * word)) (A : list (Z * Z)) : word -> bool :=
  fun a => page_in_ranges (page_base a) L && negb (page_allowedb A (page_base a)).

Lemma page_in_ranges_incl : forall p l L,
  incl l L -> page_in_ranges p l = true -> page_in_ranges p L = true.
Proof.
  intros p l L Hincl Hp. unfold page_in_ranges in *.
  apply existsb_exists in Hp as (r & Hin & Hr).
  apply existsb_exists. exists r. split; [exact (Hincl r Hin) | exact Hr].
Qed.

Lemma lazy_cover_mkH : forall L A lazy,
  incl lazy L -> lazy_cover (mkH L A) lazy A.
Proof.
  intros L A lazy Hincl w Hl Hw. unfold mkH in Hw.
  rewrite (page_in_ranges_incl _ _ _ Hincl Hl) in Hw. cbn in Hw.
  destruct (page_allowedb A (page_base w)); [reflexivity | discriminate].
Qed.

(* [comment removed for export] *)
Definition seg_top (seg : Segment) : Z :=
  (Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.

Definition wx_segs_nowrap_b (segs : list Segment) : bool :=
  forallb (fun seg => negb (seg_executable seg && seg_writable seg)
                      || (seg_top seg <=? 2 ^ 64)%Z) segs.

Lemma wx_segs_nowrap_of_b : forall segs,
  wx_segs_nowrap_b segs = true -> wx_segs_nowrap segs.
Proof.
  intros segs Hb seg Hin Hwx. unfold wx_segs_nowrap_b in Hb.
  rewrite forallb_forall in Hb. specialize (Hb seg Hin). rewrite Hwx in Hb. cbn in Hb.
  apply Z.leb_le in Hb. exact Hb.
Qed.





Lemma page_base_le : forall a, (bv_unsigned (page_base a) <= bv_unsigned a)%Z.
Proof.
  intros a. unfold page_base, page_base_of. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha.
  pose proof (Z.div_mod (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hdm.
  pose proof (Z.mod_pos_bound (bv_unsigned a) page_size ltac:(unfold page_size; lia)) as Hmb.
  assert (Hq : (0 <= bv_unsigned a / page_size)%Z)
    by (apply Z.div_pos; unfold page_size in *; lia).
  set (q := (bv_unsigned a / page_size)%Z) in *.
  change (bv_modulus 64) with (2 ^ 64)%Z in *. unfold page_size in *.
  rewrite bv_wrap_small; [lia|].
  change (bv_modulus 64) with (2 ^ 64)%Z. lia.
Qed.




(* [comment removed for export] *)
Lemma MInv_transport : forall A m m',
  MInv A m ->
  m_vm_materialized m' = m_vm_materialized m ->
  m_vm_lazy m' = m_vm_lazy m ->
  (eager_used m' + A_bytes A <= vm_limit (m_vmmaps m'))%Z ->
  MInv A m'.
Proof.
  intros A m m' [H1 H2 H3 H4 H5] Hm Hl Hb. constructor; rewrite ?Hm, ?Hl; assumption.
Qed.
End AsanAcct.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil AsCells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem := word -> option byte.

(* [comment removed for export] *)
Definition SB : Z := 0x7fff8000.
Definition AS_LO : Z := 0x7fff7000.                (* [comment removed for export] *)
Definition AS_GAPLO : Z := 0x8fff7000.             (* [comment removed for export] *)
Definition AS_GAPHI : Z := 0x2008fff7000.          (* [comment removed for export] *)
Definition AS_HEAPLO : Z := 0x10007fff8000.        (* [comment removed for export] *)
Definition PTRHI : Z := 2 ^ 47.                    (* [comment removed for export] *)
Definition PTRLO : Z := 0x1010.                    (* [comment removed for export] *)
Definition PG : Z := 4096.

(* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.
Definition GBUDGET : Z := 3 * 2 ^ 32.
Definition LMAX : Z := 64.                         (* [comment removed for export] *)
Definition NMAX : Z := 2 ^ 40.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EVT : Z := 2 ^ 28.
Definition KCAP : Z := 2 ^ 39.
Definition kcost_malloc (n : Z) : Z := EVT.        (* [comment removed for export] *)
Definition kcost_free : Z := EVT.

(* [comment removed for export] *)
Definition MSTK_A : Z := 3584.     (* [comment removed for export] *)
Definition MSTK_N : Z := 3600.     (* [comment removed for export] *)
Definition MSTK_M : Z := 2304.     (* [comment removed for export] *)
Definition MSTK_F : Z := 256.      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition MSTK_C : Z := 2816.

(* [comment removed for export] *)
Definition FS (k : Z) : Z := 64 * 2 ^ k.
Definition FCAP (k : Z) : Z := 2 ^ (14 - k).
Definition KMAXCLASS : Z := 3.     (* [comment removed for export] *)
(* [comment removed for export] *)
Definition FAKE_SIZE : Z := 0xb09000.
Definition fake_flags_off (k : Z) : Z := 0x1000 + (2 ^ 14 - 2 ^ (14 - k)) * 2.  (* [comment removed for export] *)
Definition fake_frame_addr (fs k pos : Z) : Z := fs + 0x9000 + k * 2 ^ 20 + FS k * pos.
Definition fake_flag_addr (fs k pos : Z) : Z := fs + fake_flags_off k + pos.

(* [comment removed for export] *)
Definition DMAX : nat := 6%nat.

(* [comment removed for export] *)
Definition as_callee_saved : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition in_blocks (Lc : list (Z * Z)) (z : Z) : Prop := exists b n, In (b, n) Lc /\ b <= z < b + n.
Definition in_wins (W : list (Z * Z)) (z : Z) : Prop := exists lo hi, In (lo, hi) W /\ lo <= z < hi.
(* [comment removed for export] *)
Definition in_frames (FF : list (Z * Z)) (z : Z) : Prop := exists f k, In (f, k) FF /\ f <= z < f + FS k - 8.
Definition in_frames_full (FF : list (Z * Z)) (z : Z) : Prop := exists f k, In (f, k) FF /\ f <= z < f + FS k.

(* [comment removed for export] *)
Definition sh_lo (b : Z) : Z := SB + b / 8.
Definition sh_hi (b n : Z) : Z := SB + (b + n + 7) / 8.

Definition in_block_shadow (Lc : list (Z * Z)) (z : Z) : Prop := exists b n, In (b, n) Lc /\ sh_lo b <= z < sh_hi b n.
Definition in_frame_shadow (FF : list (Z * Z)) (z : Z) : Prop := exists f k, In (f, k) FF /\ sh_lo f <= z < sh_hi f (FS k).
(* [comment removed for export] *)
Definition shmaps (z : Z) : Prop := (AS_LO <= z < AS_GAPLO) \/ (AS_GAPHI <= z < AS_HEAPLO).
(* [comment removed for export] *)
Definition in_band (z : Z) : Prop := AS_LO <= z < AS_HEAPLO.
(* [comment removed for export] *)
Definition addr_is_mem (a : Z) : Prop := (0 <= a <= SB - 1) \/ (AS_HEAPLO <= a < PTRHI).

(* [comment removed for export] *)
Fixpoint PHI (L : list (Z * Z)) : Z := match L with [] => 0 | b :: r => snd b + MBLK + PHI r end.
Lemma PHI_app : forall L1 L2, PHI (L1 ++ L2) = PHI L1 + PHI L2.
Proof. induction L1 as [|b r IH]; intros L2; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); [reflexivity | rewrite IH; lia]. Qed.
Lemma PHI_perm : forall L L', Permutation L L' -> PHI L = PHI L'.
Proof. intros L L' P. induction P; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. Qed.

(* [comment removed for export] *)
Fixpoint fcount (k : Z) (FF : list (Z * Z)) : Z :=
  match FF with [] => 0 | f :: r => (if Z.eqb (snd f) k then 1 else 0) + fcount k r end.

(* [comment removed for export] *)
Definition in_rtc (IA : as_addrs) (a : Z) : Prop :=
  (ia_rtc_sb IA <= a < ia_rtc_sb IA + 8) \/ (ia_rtc_uar IA <= a < ia_rtc_uar IA + 4).
(* [comment removed for export] *)
Definition as_wins_ok (IA : as_addrs) (W : list (Z * Z)) : Prop :=
  forall a, in_wins W a -> ia_img_lo IA <= a < ia_img_hi IA /\ ~ in_wins (ia_priv IA) a /\ ~ in_rtc IA a /\ ~ in_wins (ia_const IA) a.

(* [comment removed for export] *)
Definition sbyte (M : mem) (z : Z) : Z :=
  match M (Z_to_bv 64 z) with Some b => bv_signed b | None => -1 end.
Definition accessible (M : mem) (b n : Z) : Prop :=
  forall a, b <= a < b + n -> sbyte M (sh_lo a) = 0 \/ (a mod 8 < sbyte M (sh_lo a) <= 7).

(* [comment removed for export] *)
Definition defined (M : mem) (lo hi : Z) : Prop := forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None.
Definition m64 (M : mem) (a : Z) (w : Z) : Prop :=
  exists bs, (forall i, (i < 8)%nat -> M (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i bs (Z_to_bv 8 0)))
             /\ length bs = 8%nat /\ bytes_le_to_Z bs = w.
Inductive fpc (M : mem) : Z -> Z -> nat -> Prop :=
| fpc_stop : forall v lo d, (v <= lo \/ v mod 8 <> 0 \/ PTRHI <= v) -> fpc M v lo d
| fpc_frame : forall v lo d w, lo + 16 <= v -> v mod 8 = 0 -> v < PTRHI -> defined M (v - 16) v -> m64 M (v - 16) w ->
    fpc M w v d -> fpc M v lo (S d).



Lemma fpc_shape : forall M v lo d, fpc M v lo d -> (v <= lo \/ v mod 8 <> 0 \/ PTRHI <= v) \/ lo + 16 <= v.
Proof. intros M v lo d H. destruct H; [left; assumption | right; assumption]. Qed.

Lemma fpc_kept_gen : forall M v lo d, fpc M v lo d -> forall M' : mem,
  ((v <= lo \/ v mod 8 <> 0 \/ PTRHI <= v) \/ (forall a, v - 16 <= a < PTRHI -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) ->
  fpc M' v lo d.
Proof.
  intros M v lo d H; induction H as [v lo d ST | v lo d w H16 H8 HP DEF RD CH IH]; intros M' HYP.
  - apply fpc_stop; assumption.
  - destruct HYP as [ST | EQ]; [apply fpc_stop; exact ST|].
    apply (fpc_frame M' v lo d w); try assumption.
    + intros i Hi. rewrite EQ by lia. exact (DEF i Hi).
    + destruct RD as (bs & B1 & B2 & B3). exists bs. split; [| split; assumption].
      intros i Hi. rewrite EQ by lia. exact (B1 i Hi).
    + apply IH. destruct (fpc_shape M w v d CH) as [ST' | FR]; [left; exact ST' | right].
      intros a Ha. apply EQ. lia.
Qed.


(* [comment removed for export] *)
Definition same_except_vm (mdl mdl' : Model) : Prop :=
  mdl' = mkModelOf (m_fd mdl) (m_vm mdl') (m_io mdl) (m_fsys mdl) (m_proc mdl) (m_lim mdl) (m_time mdl).

Lemma same_except_vm_refl : forall mdl, same_except_vm mdl mdl.
Proof. intros [fd vm io fsy pr li ti]. reflexivity. Qed.
Lemma same_except_vm_frame : forall mdl mdl', same_except_vm mdl mdl' ->
  m_fds mdl' = m_fds mdl /\ m_fs mdl' = m_fs mdl /\ m_halted mdl' = m_halted mdl /\ m_fd mdl' = m_fd mdl
  /\ m_io mdl' = m_io mdl /\ m_proc mdl' = m_proc mdl /\ m_lim mdl' = m_lim mdl /\ m_time mdl' = m_time mdl.
Proof. intros mdl mdl' ->. repeat split; reflexivity. Qed.
Lemma same_except_vm_trans : forall m1 m2 m3, same_except_vm m1 m2 -> same_except_vm m2 m3 -> same_except_vm m1 m3.
Proof. (lazymatch goal with |- ?G => let G' := eval unfold same_except_vm in G in change_no_check G' end). intros m1 m2 m3 -> ->. reflexivity. Qed.
Lemma same_except_vm_of_materialized : forall m m', same_but_materialized m m' -> same_except_vm m m'.
Proof. intros m m' ->. destruct m as [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* [comment removed for export] *)
Definition lzb (mdl : Model) (a : Z) : bool := page_in_ranges (page_base (Z_to_bv 64 a)) (m_vm_lazy mdl).

(* [comment removed for export] *)
Definition cellN (SEGS : list Segment) (M : mem) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition range_allowed (AA : list (Z * Z)) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> page_allowedb AA (page_base (Z_to_bv 64 a)) = true.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
  Context {RC : run_ceil}.
  Variable IA : as_addrs.

  (* [comment removed for export] *)
  Definition dyn_ok (lo hi : Z) : Prop :=
    0 < lo /\ lo <= hi /\ hi <= CEIL /\ (hi <= ia_img_lo IA \/ ia_img_hi IA <= lo) /\ (hi <= AS_LO \/ AS_HEAPLO <= lo).

  (* [comment removed for export] *)
  Definition ablk_ok (p n : Z) : Prop :=
    PTRLO <= p /\ p + n <= CEIL /\ (p + n <= ia_img_lo IA \/ ia_img_hi IA <= p) /\ (p + n <= AS_LO \/ AS_HEAPLO <= p).

  (* [comment removed for export] *)
  Definition in_stack_shadow (z : Z) : Prop := sh_lo CEIL <= z < SB + 2 ^ 44.
  Definition in_image_shadow (z : Z) : Prop := sh_lo (ia_img_lo IA) <= z < sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA).

  (* [comment removed for export] *)
  Definition as_app_owned (W Lc FF : list (Z * Z)) (a : Z) : Prop :=
    in_blocks Lc a \/ in_frames FF a \/ CEIL <= a \/ in_wins W a
    \/ in_block_shadow Lc a \/ in_frame_shadow FF a \/ in_stack_shadow a \/ in_image_shadow a.

  (* [comment removed for export] *)
  Definition app_visible (Lc FF : list (Z * Z)) (a : Z) : Prop :=
    in_blocks Lc a \/ in_frames_full FF a \/ in_block_shadow Lc a \/ in_frame_shadow FF a
    \/ in_stack_shadow a \/ in_image_shadow a.
  (* [comment removed for export] *)
  Definition ia_errno : Z := ia_tp IA - 164.
  Definition in_errno (a : Z) : Prop := ia_errno <= a < ia_errno + 4.
  Definition as_changed (stk : Z) (Lc FF : list (Z * Z)) (sp : Z) (a : word) : Prop :=
    (sp - stk <= bv_unsigned a < sp)
    \/ (bv_unsigned a < CEIL /\ ~ (ia_img_lo IA <= bv_unsigned a < ia_img_hi IA) /\ ~ app_visible Lc FF (bv_unsigned a))
    \/ in_wins (ia_priv IA) (bv_unsigned a)
    \/ in_errno (bv_unsigned a).
  Definition errno_kept (M M' : mem) : Prop :=
    forall a : word, in_errno (bv_unsigned a) -> M a <> None -> M' a <> None.

  (* [comment removed for export] *)
  Definition lazy_kept (Lc FF : list (Z * Z)) (mdl mdl' : Model) : Prop :=
    forall a, (app_visible Lc FF a \/ CEIL <= a < 2 ^ 64 \/ (ia_img_lo IA <= a < ia_img_hi IA)) -> lzb mdl' a = lzb mdl a.

  (* [comment removed for export] *)
  Definition shadow_visible (Lc FF : list (Z * Z)) (b n : Z) : Prop :=
    forall z, b <= z < b + n ->
      in_blocks Lc z \/ (exists f k, In (f, k) FF /\ f <= z < f + FS k - 8) \/ (CEIL <= z < PTRHI) \/ (ia_img_lo IA <= z < ia_img_hi IA).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable AAINV : list (Z * Z) -> list (Z * Z) -> Z -> Z -> Z -> mem -> Model -> Prop.
  (* [comment removed for export] *)
  Variable fsbase : Z.

  (* [comment removed for export] *)
  Definition SHC : list (Z * Z) :=
    [(sh_lo CEIL, SB + 2 ^ 44); (sh_lo (ia_img_lo IA), sh_hi (ia_img_lo IA) (ia_img_hi IA - ia_img_lo IA));
     (sh_lo fsbase, sh_hi fsbase FAKE_SIZE)].

  (* [comment removed for export] *)
  Definition AAINV_frame_stmt : Prop := forall W Lc FF B C K M M' mdl,
    as_wins_ok IA W ->
    AAINV Lc FF B C K M mdl ->
    (forall a : word, M' a <> M a -> as_app_owned W Lc FF (bv_unsigned a) /\ M' a <> None) ->
    AAINV Lc FF B C K M' mdl.
  (* [comment removed for export] *)
  Definition AAINV_model_stmt : Prop := forall Lc FF B C K M mdl mdl',
    AAINV Lc FF B C K M mdl -> m_vm mdl' = m_vm mdl -> AAINV Lc FF B C K M mdl'.
  (* [comment removed for export] *)
  Definition AAINV_mono_stmt : Prop := forall Lc FF B C K B' C' K' M mdl,
    AAINV Lc FF B C K M mdl -> B <= B' -> C <= C' -> K <= K' -> AAINV Lc FF B' C' K' M mdl.
  (* [comment removed for export] *)
  Definition AAINV_lazy_stmt : Prop := forall Lc FF B C K M mdl,
    AAINV Lc FF B C K M mdl ->
    exists AA, A_wf AA /\ MInv AA mdl
      /\ (forall lo hi, In (lo, hi) SHC -> range_allowed AA lo hi)
      /\ (forall b n, In (b, n) Lc -> range_allowed AA (sh_lo b) (sh_hi b n))
      /\ (forall mdl', MInv AA mdl' -> same_but_materialized mdl mdl' -> AAINV Lc FF B C K M mdl').
  (* [comment removed for export] *)
  Definition AAINV_zone_stmt : Prop := forall Lc FF B C K M mdl b n,
    AAINV Lc FF B C K M mdl -> In (b, n) Lc -> ablk_ok b n /\ 1 <= n /\ b mod 16 = 0.
  Definition AAINV_disj_stmt : Prop := forall Lc FF B C K M mdl L1 L2 b n b' n',
    AAINV Lc FF B C K M mdl -> Lc = L1 ++ (b, n) :: L2 -> In (b', n') (L1 ++ L2) -> b + n <= b' \/ b' + n' <= b.
  Definition AAINV_perm_stmt : Prop := forall Lc Lc' FF FF' B C K M mdl,
    Permutation Lc Lc' -> Permutation FF FF' -> AAINV Lc FF B C K M mdl -> AAINV Lc' FF' B C K M mdl.
  Definition AAINV_fzone_stmt : Prop := forall Lc FF B C K M mdl f k,
    AAINV Lc FF B C K M mdl -> In (f, k) FF ->
    0 <= k <= KMAXCLASS /\ ablk_ok f (FS k) /\ f mod FS k = 0
    /\ fsbase + 0x9000 <= f /\ f + FS k <= fsbase + FAKE_SIZE.
  Definition AAINV_fdisj_stmt : Prop := forall Lc FF B C K M mdl F1 F2 f k f' k',
    AAINV Lc FF B C K M mdl -> FF = F1 ++ (f, k) :: F2 -> In (f', k') (F1 ++ F2) -> f + FS k <= f' \/ f' + FS k' <= f.
  Definition AAINV_bfdisj_stmt : Prop := forall Lc FF B C K M mdl b n f k,
    AAINV Lc FF B C K M mdl -> In (b, n) Lc -> In (f, k) FF -> b + n <= f \/ f + FS k <= b.
  Definition AAINV_bounds_stmt : Prop := forall Lc FF B C K M mdl,
    AAINV Lc FF B C K M mdl -> 0 <= PHI Lc <= B /\ Z.of_nat (length Lc) <= C /\ 0 <= K /\ List.NoDup Lc /\ List.NoDup FF.
  (* [comment removed for export] *)
  Definition AAINV_lazyzone_stmt : Prop := forall Lc FF B C K M mdl,
    AAINV Lc FF B C K M mdl ->
    Forall (fun iv : word * word => 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
            /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo IA \/ ia_img_hi IA <= bv_unsigned (fst iv))) (m_vm_lazy mdl).
  (* [comment removed for export] *)
  Definition AAINV_nolazy_stmt : Prop := forall Lc FF B C K M mdl z,
    AAINV Lc FF B C K M mdl -> in_blocks Lc z \/ in_frames_full FF z -> lzb mdl z = false.
  (* [comment removed for export] *)
  Definition AAINV_shdef_stmt : Prop := forall Lc FF B C K M mdl z,
    AAINV Lc FF B C K M mdl -> shmaps z -> M (Z_to_bv 64 z) <> None.
  (* [comment removed for export] *)
  Definition AAINV_cells_stmt (SEGS : list Segment) : Prop := forall Lc FF B C K M mdl,
    AAINV Lc FF B C K M mdl ->
    (forall b n a, In (b, n) Lc -> (b <= a < b + n \/ sh_lo b <= a < sh_hi b n) ->
        M (Z_to_bv 64 a) <> None /\ store_ok SEGS M (Z_to_bv 64 a) 1%nat = true)
    /\ (forall f k a, In (f, k) FF -> (f <= a < f + FS k - 8 \/ sh_lo f <= a < sh_hi f (FS k)) ->
        M (Z_to_bv 64 a) <> None /\ store_ok SEGS M (Z_to_bv 64 a) 1%nat = true)
    /\ cellN SEGS M (ia_rtc_sb IA) 8 SB /\ cellN SEGS M (ia_rtc_uar IA) 4 1.

  Record AAINV_props (SEGS : list Segment) : Prop := AAP {
    aap_frame : AAINV_frame_stmt;   aap_model : AAINV_model_stmt;  aap_mono : AAINV_mono_stmt;  aap_lazy : AAINV_lazy_stmt;
    aap_zone : AAINV_zone_stmt;     aap_disj : AAINV_disj_stmt;    aap_perm : AAINV_perm_stmt;
    aap_fzone : AAINV_fzone_stmt;   aap_fdisj : AAINV_fdisj_stmt;  aap_bfdisj : AAINV_bfdisj_stmt;
    aap_bounds : AAINV_bounds_stmt; aap_lazyzone : AAINV_lazyzone_stmt; aap_cells : AAINV_cells_stmt SEGS;
    aap_nolazy : AAINV_nolazy_stmt; aap_shdef : AAINV_shdef_stmt }.
End WithCeil.

(* [comment removed for export] *)
Lemma band_lits : AS_LO < SB /\ SB < AS_GAPLO /\ AS_GAPLO < AS_GAPHI /\ AS_GAPHI < AS_HEAPLO /\ AS_HEAPLO < PTRHI.
Proof. (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, SB, AS_GAPLO, AS_GAPHI, AS_HEAPLO, PTRHI in G in change_no_check G' end). lia. Qed.


