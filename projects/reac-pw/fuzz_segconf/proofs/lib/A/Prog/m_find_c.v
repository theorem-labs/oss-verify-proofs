(* m_find (fuzz_segconf.c:150-156; fuzz_segconf.asan 0x87538, 176 bytes, 44 instructions; frame 48 bytes, no
   side-stack frame): the contract of the ASan build's code, in plugin-hostd/fuzz_command's lib/A/Prog form
   (afn_pre at the entry, SRr of apost_base at the return).
   Functional content: the plain contract lib/Prog/m_find_c.v:10-60 (m_find_ptr :40-41, m_find_pre :43-46,
   the post :53-54), restated over the ASan reader. The post is the plain one: a0 = m_find_ptr c mc (seg_spec.zs l),
   i.e. seg_spec.mseg_addr c i for SegModel.m_find mc (zs l) = Some i, else 0, l the n bytes at name. m_find_ptr is
   the plain file's Definition, restated below with the same body (the plain file Requires the plain image module
   Img0, so it cannot be Required here).
   What the code does (objdump of fuzz_segconf.asan, 0x87538-0x875e4): s3 = c->n (lw of c + 0x2000 at 0x87580);
   c->n <= 0 returns NULL (blez 0x87584); else for i = 0 .. c->n - 1 (s0 = c + 256 i, addi 0x875ac):
   strlen(c->seg[i].name) (jal 0x8758c to the strlen trampoline) <> n goes on (bne 0x87590); else
   bcmp(c->seg[i].name, name, n) (jal 0x875a0 to the bcmp trampoline) = 0 returns &c->seg[i] (beqz 0x875a4);
   none returns NULL (0x875b4). It reads c->n, the names of seg[0 .. n) (each with strlen's slack, inside the
   16-byte name field: c is 16-aligned) and at most n bytes at name; it writes its own frame only, so its footprint
   is []. No abort site (provenance/evidence/image-tables/program.asan.tsv line 13).
   What it reads besides: the shadow base, through the GOT word as_got_shadow B (image A 0xa2a50, ld at 0x8755c),
   whose value and target AR gives (AR_const_law, lib/Reusable/YG0d.v:469-475), so the contract names neither.
   ASAN FACTS ADDED over the plain contract:
   - inline check 1, load4 of c->n at c + 0x2000 (shadow test 0x8756c-0x8757c, slow path 0x875d8, error arm
     __asan_report_load4 at 0x875e4): killed by m_find_pre's sa_addr rd c SEG_M_SIZE (0x2000 + 4 <= 9236).
   - strlen's range [c + 256 i, ... + length + 1) and bcmp's first range [c + 256 i, + n) lie in the block (a name
     is at most 15 bytes, mconf_encp's cstr_enc 16): the same sa_addr. bcmp's second range [name, name + n): killed
     by sa_addr rd name n. The kit's abcmp_realizes (lib/Reusable/YG0d.v:361-380) asks both ranges addressable and
     apart from its 2 * ESTACK window, and n < 2 ^ 32: n = strlen(name_i) <= 15 on the only path that calls it.
   - where each object lies: the block by sa_heap (calloc(1, 0x2414) at LLVMFuzzerTestOneInput 0x84f94,
     PREMISES-A.md section 2.3), never by an address bound against the image's end; name by sa_loc (m_file passes
     a pointer into its text block, a heap block; LLVMFuzzerTestOneInput passes its probe buffer, in its class-3
     side-stack frame, and the literal at 0x21040). The real stack window [sp - STK, sp) is apart from all three
     places, so the plain apart premises are not restated (reac_segconf_find_c.v gives the kit facts).
   - arodata_okP over the read-only window RLO RHI, a contract parameter (each image's walk gives its RELRO
     bounds): row 16 asks rt_rom_view (fuzz_command lib/A/Rt/RtDefs.v:145), which AR does not give.
   - no side-stack frame and no printf: apost_base, EV_m_find = 0, post tail sa_noalloc.
   Call sites (provenance/evidence/image-tables/callsites.asan.tsv lines 116, 37, 40): m_file 0x86ac8 (a0 = c, a1 = the stripped
   name in the text block, a2 = its length, 1 <= n <= 15 by the bgeu at 0x86ab8); LLVMFuzzerTestOneInput 0x85734
   and 0x85790 (a1 = 0x21040).
   image A: A_m_find = 0x87538; STK_m_find = 48 + 2 * ESTACK (INFERENCE: its frame and the 2 * ESTACK window
   abcmp_realizes asks, YG0d.v:364, the deeper of its two callees).
   IMAGE-INDEPENDENT: no image module is Required; A_m_find, STK_m_find, RLO and RHI are parameters, and the
   shadow-base cells are fields of B.
   The WALK takes these runtime entries as Section hypotheses:
     RtString.astrlen_realizes, the interceptor lane's interface row 16 (in the accepted v1, 5e0b8a44fdc; at
     e45889d6935a strlen is DECISION 2, option (b), of provenance/evidence/interceptors/INTERFACE-A-interceptors.md
     (commit 7068323e2626)), at the strlen trampoline (image A 0x43a0c, interceptor 0x43abc);
     the kit's abcmp_realizes (the image-A owner's frame; lib/Reusable/YG0d.v:361), at the bcmp trampoline (image A
     0x43a38, interceptor 0x46e80).
   They are NOT premises of this contract: the statement does not mention them. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* &c->seg[i] for the spine's m_find, else NULL (the plain lib/Prog/m_find_c.v:40-41, the same body) *)
Definition m_find_ptr (c : Z) (mc : mconf) (name : list Z) : Z :=
match SegModel.m_find mc name with Some i => seg_spec.mseg_addr c i | None => 0 end.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Section d.
Variable B : asyms.
(* The plain m_find_pre (lib/Prog/m_find_c.v:43-46) over the reader rd = aview segs (w_H W) mem: c the mconf block,
   nonzero, 16-aligned, holding mc, a live heap block of 9236 bytes, addressable; the n bytes l at name, in a heap
   block, a side-stack frame or the image, addressable. The plain stack_ok / apart / mem_inv conjuncts are
   afn_pre's and the locations' here. Outside the sections: m_find_pre segs B ly S rd c name n mc l. *)
Definition m_find_pre (ly : alayout) (S : astate) (rd : reader) (c name n : Z) (mc : mconf) (l : list byte)
: Prop :=
c <> 0 /\ c mod 16 = 0 /\ sa_mconf rd c mc /\ sa_heap B ly S c seg_spec.SEG_M_SIZE /\
sa_addr rd c seg_spec.SEG_M_SIZE /\
sa_bytes rd name l /\ Z.of_nat (length l) = n /\ sa_addr rd name n /\ sa_loc segs B ly S name n.
(* the events this call spends: 0, it reaches no allocator entry *)
Definition EV_m_find : Z := 0.
Definition m_find_contract (A_m_find STK_m_find RLO RHI : Z) : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (c name n : Z) (mc : mconf) (l : list byte),
afn_pre segs B STK_m_find ly S W regs mem md ch ->
arodata_okP segs RLO RHI B (aview segs (w_H W) mem) ->
getr regs 10 = w64 c -> 0 <= c < 2 ^ 64 -> getr regs 11 = w64 name -> 0 <= name < 2 ^ 64 ->
getr regs 12 = w64 n -> 0 <= n < 2 ^ 64 ->
m_find_pre ly S (aview segs (w_H W) mem) c name n mc l ->
st_nev S + EV_m_find <= EV_MAX ->
SRr segs W (cfg_at segs A_m_find regs mem md)
(apost_base segs B STK_m_find [] regs ly S W mem md EV_m_find
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (m_find_ptr c mc (seg_spec.zs l)) /\
 sa_kept segs W mem W' mem' regs STK_m_find (fun _ => False) /\
 sa_noalloc B ly S ly' S')).
End d.
End c.
End b.
