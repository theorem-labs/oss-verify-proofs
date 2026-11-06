(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AFib.v, with its module paths and module names changed; 66 of its 84 lines of code are new or changed and 251 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/ImgBaseAGS.v (commit 30a1993588f, c5 + memnorm; file sha256 477c5dbd27dc) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/ImgBaseAGS.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* The image-free part of the secondary interface AGif4.AIfaceS (n >= 64513, the LargeMmapAllocator path).

   - [AImgS]: the class of the image facts AIfaceS names beyond ImgBase.AImg: the shadow offset, the image addresses
     in the const zone of the secondary walk (AGif4.CZS), the depot's write zone, StackDepotPut's entry pc, the zones
     of a kernel grant, and the walk's frame at Allocate's entry.  AGif4 takes it as [Context {IMS : AImgS}] (after
     [{IM : AImg}]), so a consumer's explicit arguments do not move; cgif_file's instance is AGif4cgif.AImgS_cgif.
   - copies of the image-free definitions AGif4 borrows from image files (AGjm's geometry of the secondary block,
     AGhy.AFSTACK, YFl0.DEP_STK, YF06.NOB, YFib's model state after the secondary allocation, AGif0n.malloc_K_t).
     Each copy has its original's text and section variables in the original's order, so each copy is convertible
     with its original; AGjm's SMv / PBv / WINM / WIN are copies too, over [SHBv] below (the class's shadow offset)
     in place of AGjm.SHBv. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The image facts of the secondary interface.                                                                      *)
Class AImgS : Type := MkAImgS {
  (* the shadow offset (cgif: AGjm.SHBv): [SHBv] below, hence SMv / PBv / WINM / WIN *)
  ims_shb : Z;
  (* the bounds of the const zone (AGif4.CZS, after AGif0cgif.CZONE) that are image addresses: the image's end (cgif:
     YF0x.TFIB_IMG_END) and the end of the shadow window that starts at [ims_shb] *)
  ims_img_end : Z; ims_csh_end : Z;
  (* the depot's write zone (cgif: AGjm.DZONE) *)
  ims_dzone : alayout -> Z -> Prop;
  (* StackDepotPut's entry pc (cgif: YFl0.A_StackDepotPut) *)
  ims_depot : Z;
  (* the zones a kernel grant lies in (cgif: YF0x.zone3) *)
  ims_zone3 : Z -> Z -> Prop;
  (* the walk's frame at Allocate's entry (cgif: AGif0cgif.wframe) *)
  ims_wframe : world im_segs -> alayout -> bvmap 5 word -> (word -> option byte) -> list Z -> Prop
}.
Context {IMS : AImgS}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Stack sizes and the kernel's grant bound.                                                                        *)

(* copy of AGhy.v:38, remove when AGhy.v is ported *)
Definition AFSTACK : Z := 4096.
(* copy of YFl0.v:58, remove when YFl0.v is ported *)
Definition DEP_STK : Z := 512.
(* copy of YF06.v:74, remove when YF06.v is ported *)
Definition NOB : Z := 536870912.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The geometry of the secondary block (AGjm's Section g, over the variables these definitions use, in AGjm's order). *)
(* The shadow offset: the class's field, in place of AGjm.SHBv. *)
Definition SHBv : Z := ims_shb.
Section g.
Variables (ly : alayout) (regs0 : bvmap 5 word) (n : Z) (idx : Z) (mb : Z).
(* copy of AGjm.v:151, remove when AGjm.v is ported *)
Let sp0 : Z := bv_unsigned (getr regs0 2).
(* copy of AGjm.v:155, remove when AGjm.v is ported *)
Let INSTv : Z := bv_unsigned (getr regs0 11).
(* copy of AGjm.v:156, remove when AGjm.v is ported *)
Let T : Z := ly_T ly.
(* copy of AGjm.v:158, remove when AGjm.v is ported *)
Let Qb : Z := ly_Q ly.
(* copy of AGjm.v:159, remove when AGjm.v is ported *)
Definition R8v : Z := (n + 7) / 8 * 8.
(* copy of AGjm.v:160, remove when AGjm.v is ported *)
Definition N8D : Z := n / 8 * 8.
(* copy of AGjm.v:161, remove when AGjm.v is ported *)
Definition NDv : Z := R8v + 4096.
(* copy of AGjm.v:162, remove when AGjm.v is ported *)
Definition MSv : Z := (NDv + 4095) / 4096 * 4096 + 4096.
(* copy of AGjm.v:164, remove when AGjm.v is ported *)
Definition QSv : Z := Qb + 8 * idx.
(* copy of AGjm.v:165, remove when AGjm.v is ported *)
Definition Kv : Z := mb + 4096.
(* copy of AGjm.v:166, remove when AGjm.v is ported *)
Definition Uv : Z := mb + 6144.
(* copy of AGjm.v:169, remove when AGjm.v is ported *)
Definition UEv : Z := mb + 6144 + R8v.
(* copy of AGjm.v:171, remove when AGjm.v is ported *)
Definition SMv : Z := SHBv + mb / 8.
(* copy of AGjm.v:172, remove when AGjm.v is ported *)
Definition PBv : Z := SHBv + (mb + 6144 + N8D) / 8.
(* copy of AGjm.v:173, remove when AGjm.v is ported *)
Definition LGv : Z := Z.log2 (MSv / 4096) + 12.
(* copy of AGjm.v:175, remove when AGjm.v is ported *)
Definition BSLv : Z := INSTv + 168 + 8 * LGv.
(* copy of AGjm.v:343, remove when AGjm.v is ported *)
Definition WINT (a : Z) : Prop :=
(T + 2768 <= a < T + 2824) \/ (T + 2872 <= a < T + 2888) \/ (T + 2904 <= a < T + 2912) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
(* copy of AGjm.v:347, remove when AGjm.v is ported *)
Definition WINI (a : Z) : Prop :=
(INSTv + o_sec_reserved <= a < INSTv + o_sec_sorted + 1) \/ (INSTv + o_sec_stats <= a < INSTv + o_sec_stats + 32) \/
(BSLv <= a < BSLv + 8) \/ (INSTv + o_sec_mutex <= a < INSTv + o_sec_mutex + 4) \/ (INSTv + o_comb_stats <= a < INSTv + o_comb_stats + 40).
(* copy of AGjm.v:350, remove when AGjm.v is ported *)
Definition WINM (a : Z) : Prop := (QSv <= a < QSv + 8) \/ (mb <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8).
(* copy of AGjm.v:351, remove when AGjm.v is ported *)
Definition WIN (a : Z) : Prop := (sp0 - AFSTACK <= a < sp0) \/ WINT a \/ WINI a \/ WINM a.
(* copy of AGjm.v:353, remove when AGjm.v is ported *)
Definition WINP (a : Z) : Prop := (sp0 - AFSTACK <= a < sp0) \/ WINT a \/ WINI a.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model's state after the secondary allocation (YFib's Section u). *)
Section u.
Variables (S : astate) (n : Z) (tr : list Z) (z : Z) (ms nd : Z) (grow : bool).
(* copy of YFib.v:232, remove when YFib.v is ported *)
Definition rS : nat := length (st_secs S).
(* copy of YFib.v:233, remove when YFib.v is ported *)
Definition KS : chunk := mkChunk (PSec rS kPage) n CAllocated.
(* copy of YFib.v:234, remove when YFib.v is ported *)
Definition resF : Z := if grow then st_sec_reserved S + kPtrArrayEntriesPerCommit else st_sec_reserved S.
(* copy of YFib.v:235, remove when YFib.v is ported *)
Definition depF : list (list Z) := if z =? 0 then st_depot S else st_depot S ++ [tr].
(* copy of YFib.v:236, remove when YFib.v is ported *)
Definition sfinal : astate :=
mkA (st_regions S) (st_cache_inited S) (st_cache S) (st_chunks S ++ [KS]) (st_secs S ++ [mkSec ms nd true]) (st_sec_arr S ++ [rS]) resF
(st_qthread S) (st_qglobal S) (st_fs S) depF (st_internal_inited S) (st_nev S + 1).
End u.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cache join's tail with the spin tag of the shadow-remap refusal as a parameter (AGif0n's). *)
Section m.
Local Open Scope am_scope.
(* copy of AGif0n.v:129, remove when AGif0n.v is ported *)
Definition malloc_K_t (stag : Z) (n : Z) (trace : list Z) (ob : option sptr) : M sptr :=
match ob with
| None => ret PNull
| Some beg =>
depot_put trace ;;
let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin stag
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)
end.
End m.
End a.
