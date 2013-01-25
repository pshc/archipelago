from base import *
import os
import subprocess

ARM_IOS_VERSION = '6.0'

TargetArch = DT('TargetArch', ('name', str),
                              ('ptrSize', int),
                              ('abiAttrs', str),
                              ('cFlags', [str]),
                              ('dataLayout', str),
                              ('targetTriple', str))

def host_arch():
    name = os.uname()[4]
    ptrSize, abiAttrs = {
        'x86': (4, ''),
        'x86_64': (8, ' uwtable'),
    }[name]
    return TargetArch(name, ptrSize, abiAttrs, [], '', '')


def arm_cross_compiler():
    if os.sys.platform != 'darwin':
        print "Need arm eabi target..."

    try:
        devRoot = subprocess.check_output(['xcode-select', '-print-path'])
    except OSError, e:
        assert e.errno != 2, "Couldn't find xcode-select"
        raise
    sysRoot = os.path.join(devRoot.strip(), 'Platforms', 'iPhoneOS.platform',
            'Developer', 'SDKs', 'iPhoneOS' + ARM_IOS_VERSION + '.sdk')

    cFlags = ['-arch', 'armv7', '-miphoneos-version-min=' + ARM_IOS_VERSION,
            '-isysroot', sysRoot]
    dataLayout = "e-p:32:32:32-i1:8:32-i8:8:32-i16:16:32-i32:32:32-i64:32" + \
            ":64-f32:32:32-f64:32:64-v64:32:64-v128:32:128-a0:0:32-n32-S32"
    triple = "thumbv7-apple-ios%s.0" % (ARM_IOS_VERSION,)

    return TargetArch('arm', 4, '', cFlags, dataLayout, triple)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
